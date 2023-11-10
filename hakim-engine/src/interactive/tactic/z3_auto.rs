use std::{cell::Cell, collections::HashSet, rc::Rc, sync::Mutex, time::Duration};

use im::HashMap;
use num_bigint::BigInt;

use z3::{
    ast::{self, forall_const, Ast, Bool, Dynamic, Set},
    Config, Context, FuncDecl, SatResult, Solver, Sort, Symbol, Tactic,
};

use crate::{
    analysis::arith::{sigma_to_arith, SigmaSimplifier},
    app_ref,
    brain::{
        detect::{
            detect_char, detect_char_ty, detect_list_ty, detect_r_ty, detect_set_ty, detect_string,
            detect_z_ty,
        },
        remove_unused_var, type_of, Abstraction, Term, TermRef,
    },
    interactive::Frame,
    library::prelude::{abs, chr, minus, r},
};

use super::{Error::CanNotSolve, Result};

pub fn z3_auto(frame: Frame) -> Result<Vec<Frame>> {
    if z3_can_solve(frame) {
        Ok(vec![])
    } else {
        Err(CanNotSolve("z3"))
    }
}

#[derive(Default)]
struct Z3Names(Cell<HashMap<TermRef, usize>>);

fn lookup_in_cell_hashmap(x: &Cell<HashMap<TermRef, usize>>, key: TermRef) -> usize {
    let mut h = x.take();
    let prev_len = h.len();
    let r = *h.entry(key).or_insert(prev_len);
    x.set(h);
    r
}

fn check_exists_and_insert(x: &Cell<HashSet<usize>>, key: usize) -> bool {
    let mut h = x.take();
    let ex = h.insert(key);
    x.set(h);
    !ex
}

struct Z3Manager<'a> {
    ctx: &'a Context,
    unknowns: Z3Names,
    finite_axioms: Cell<HashSet<usize>>,
    solver: Solver<'a>,
    is_calculator: bool,
}

impl<'a> SigmaSimplifier for &Z3Manager<'a> {
    type T = ast::Int<'a>;

    fn handle_sigma_atom(self, r: TermRef, f: TermRef) -> Self::T {
        let id = lookup_in_cell_hashmap(&self.unknowns.0, f);
        let f = FuncDecl::new(
            self.ctx,
            format!("$sigma{id}"),
            &[&Sort::int(self.ctx)],
            &Sort::int(self.ctx),
        );
        f.apply(&[&self.handle_term(r)]).try_into().unwrap()
    }

    fn minus(self, x: Self::T, y: Self::T) -> Self::T {
        x - y
    }

    fn mult(self, x: Self::T, y: Self::T) -> Self::T {
        x * y
    }

    fn plus(self, x: Self::T, y: Self::T) -> Self::T {
        x + y
    }

    fn handle_term(self, t: TermRef) -> Self::T {
        self.convert_int_term(t, &[]).unwrap()
    }
}

impl<'a> Z3Manager<'a> {
    fn covert_prop_to_z3_bool(
        &self,
        t: TermRef,
        bound_variable: &[Sort<'a>],
    ) -> Option<ast::Bool<'a>> {
        if let Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) = t.as_ref()
        {
            if let Some(body) = remove_unused_var(body.clone()) {
                let op1 = self.covert_prop_to_z3_bool(var_ty.clone(), bound_variable)?;
                let op2 = self.covert_prop_to_z3_bool(body, bound_variable)?;
                return Some(op1.implies(&op2));
            }
        }
        if let Term::App { func, op: op2 } = t.as_ref() {
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "and" || unique_name == "or" {
                        let op1 = &self.covert_prop_to_z3_bool(op1.clone(), bound_variable)?;
                        let op2 = &self.covert_prop_to_z3_bool(op2.clone(), bound_variable)?;
                        let values = &[op1, op2];
                        return Some(match unique_name.as_str() {
                            "and" => ast::Bool::and(self.ctx, values),
                            "or" => ast::Bool::or(self.ctx, values),
                            _ => unreachable!(),
                        });
                    }
                }
            }
        }
        if let Term::Axiom { unique_name, .. } = t.as_ref() {
            if unique_name == "False" || unique_name == "True" {
                return Some(ast::Bool::from_bool(
                    self.ctx,
                    match unique_name.as_str() {
                        "True" => true,
                        "False" => false,
                        _ => unreachable!(),
                    },
                ));
            }
        }
        if let Term::App { func, op: op2 } = t.as_ref() {
            let op2 = op2.clone();
            if let Term::App { func, op: op1 } = func.as_ref() {
                let op1 = op1.clone();
                if let Term::App { func, op: ty } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        match unique_name.as_str() {
                            "eq" => {
                                let op1 = self.convert_general_term(op1, bound_variable)?;
                                let op2 = self.convert_general_term(op2, bound_variable)?;
                                return Some(op1._safe_eq(&op2).unwrap());
                            }
                            "inset" => {
                                let op2 = self.convert_set_term(op2, bound_variable)?;
                                let op1 = self.convert_general_term(op1, bound_variable)?;
                                dbg!(op2.get_sort().clone());
                                dbg!(op1.get_sort().clone());
                                return Some(op2.member(&op1));
                            }
                            "inlist" => {
                                let ls = self.convert_list_term(op2, bound_variable)?;
                                let elem = self.convert_general_term(op1, &[])?;
                                return Some(ls.contains(&ast::Seq::unit(self.ctx, &elem)));
                            }
                            "included" => {
                                let op2 = self.convert_set_term(op2, bound_variable)?;
                                let op1 = self.convert_set_term(op1, bound_variable)?;
                                return Some(op1.set_subset(&op2));
                            }
                            "lt" => {
                                if detect_z_ty(ty) {
                                    let op1 = self.convert_int_term(op1, bound_variable)?;
                                    let op2 = self.convert_int_term(op2, bound_variable)?;
                                    return Some(op1.lt(&op2));
                                }
                                if detect_r_ty(ty) {
                                    let op1 = self.convert_real_term(op1, bound_variable)?;
                                    let op2 = self.convert_real_term(op2, bound_variable)?;
                                    return Some(op1.lt(&op2));
                                }
                            }
                            _ => (),
                        }
                    }
                }
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    match unique_name.as_str() {
                        "divide" => {
                            let op1 = self.convert_int_term(op1, bound_variable)?;
                            let op2 = self.convert_int_term(op2, bound_variable)?;
                            let exp = op2
                                .modulo(&op1)
                                ._safe_eq(&ast::Int::from_i64(self.ctx, 0))
                                .ok()?;
                            return Some(exp);
                        }
                        "finite" => {
                            let x = self.get_finite_for_sort(op1)?;
                            let set = self.convert_general_term(op2, bound_variable)?;
                            return Some(x.apply(&[&set]).try_into().unwrap());
                        }
                        _ => (),
                    }
                }
            }
        }
        Some(
            self.generate_unknown(t, Sort::bool(self.ctx))
                .try_into()
                .unwrap(),
        )
    }

    fn generate_unknown(&self, key: TermRef, sort: Sort<'a>) -> ast::Dynamic<'a> {
        let id = lookup_in_cell_hashmap(&self.unknowns.0, key);
        ast::Dynamic::new_const(self.ctx, format!("$x{id}"), &sort)
    }

    fn convert_int_term(&self, t: TermRef, bound_variable: &[Sort<'a>]) -> Option<ast::Int<'a>> {
        Some(
            self.convert_general_term(t, bound_variable)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    fn convert_set_term(&self, t: TermRef, bound_variable: &[Sort<'a>]) -> Option<ast::Set<'a>> {
        Some(
            self.convert_general_term(t, bound_variable)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    fn convert_real_term(&self, t: TermRef, bound_variable: &[Sort<'a>]) -> Option<ast::Real<'a>> {
        Some(
            self.convert_general_term(t, bound_variable)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    fn convert_string_term(
        &self,
        t: TermRef,
        bound_variable: &[Sort<'a>],
    ) -> Option<ast::String<'a>> {
        Some(
            self.convert_general_term(t, bound_variable)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    fn convert_list_term(&self, t: TermRef, bound_variable: &[Sort<'a>]) -> Option<ast::Seq<'a>> {
        Some(
            self.convert_general_term(t, bound_variable)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    fn convert_array_term(&self, t: TermRef) -> Option<ast::Array<'a>> {
        let mut bound_variable = vec![];
        let mut names = vec![];
        let mut term_body = t;
        while let Term::Fun(a) = term_body.as_ref() {
            let sort = self.convert_sort(&a.var_ty)?;
            bound_variable.push(sort);
            names.push(
                a.hint_name
                    .clone()
                    .unwrap_or(format!("$arg{}", names.len())),
            );
            term_body = a.body.clone();
        }
        let body = self.convert_general_term(term_body, &bound_variable)?;
        if bound_variable.is_empty() {
            let t = body.as_array()?;
            return Some(t);
        }
        let names: Vec<_> = names.into_iter().map(Symbol::from).collect();
        let sorts: Vec<_> = bound_variable.iter().rev().collect();
        return Some(ast::Array::lambda(self.ctx, &names, &sorts, body));
    }

    #[allow(clippy::single_match)]
    fn convert_general_term(
        &self,
        t: TermRef,
        bound_variable: &[Sort<'a>],
    ) -> Option<ast::Dynamic<'a>> {
        match t.as_ref() {
            Term::Axiom { ty, unique_name } => {
                if self.is_calculator {
                    return None;
                }
                let sort = self.convert_sort(ty)?;
                return Some(ast::Dynamic::new_const(
                    self.ctx,
                    unique_name.as_str(),
                    &sort,
                ));
            }
            Term::Universe { .. } => (),
            Term::Forall(_) => todo!(),
            Term::Fun(_) => (),
            Term::Var { index } => {
                let sort = bound_variable.get(*index)?;
                return Some(ast::Dynamic::bound_varible(self.ctx, *index as u8, sort));
            }
            Term::Number { value } => {
                let x = ast::Int::from_i64(self.ctx, value.try_into().ok()?);
                return Some(x.into());
            }
            Term::NumberR { value, point } => {
                let x = ast::Real::from_real(
                    self.ctx,
                    value.try_into().ok()?,
                    (*point < 10).then(|| 10_i32.pow(*point as u32))?,
                );
                return Some(x.into());
            }
            Term::App { func, op: op2 } => {
                match func.as_ref() {
                    Term::Axiom { unique_name, .. } => {
                        if unique_name == "set_empty" {
                            return Some(
                                ast::Set::empty(self.ctx, &self.convert_sort(op2)?).into(),
                            );
                        }
                        if unique_name == "nil" {
                            if detect_char_ty(op2) {
                                let emp = ast::String::from_str(self.ctx, "").ok()?;
                                return Some(emp.into());
                            } else {
                                let sort = self.convert_sort(op2)?;
                                return Some(ast::Seq::empty(self.ctx, &sort).into());
                            }
                        }
                        if unique_name == "chr" {
                            let c = detect_char(&t)?;
                            let c = ast::String::from_str(self.ctx, c.to_string().as_str()).ok()?;
                            let c = unsafe { ast::Seq::wrap(self.ctx, c.get_z3_ast()) };
                            return Some(c.nth(&ast::Int::from_i64(self.ctx, 0)));
                        }
                        if unique_name == "sqrt" {
                            let op2 = self.convert_real_term(op2.clone(), bound_variable)?;
                            return Some(op2.power(&ast::Real::from_real(self.ctx, 5, 10)).into());
                        }
                        if unique_name == "abs" {
                            let op2 = self.convert_real_term(op2.clone(), bound_variable)?;
                            return Some(
                                (op2.clone()
                                    .ge(&ast::Real::from_real(self.ctx, 0, 1))
                                    .ite(&op2.clone(), &(-op2)))
                                .into(),
                            );
                        }
                    }
                    Term::App { func, op: op1 } => match func.as_ref() {
                        Term::App { func, op } => match func.as_ref() {
                            Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                                "sigma" => {
                                    return Some(
                                        sigma_to_arith::<_, BigInt>(
                                            op.clone(),
                                            op1.clone(),
                                            op2.clone(),
                                            self,
                                        )
                                        .into(),
                                    );
                                }
                                // "cnt" => {
                                //     return cnt_to_arith(op.clone(), op1.clone(), op2.clone(), arena);
                                // }
                                "union" => {
                                    let op2 = self.convert_set_term(op2.clone(), bound_variable)?;
                                    let op1 = self.convert_set_term(op1.clone(), bound_variable)?;
                                    return Some(
                                        ast::Set::set_union(self.ctx, &[&op1, &op2]).into(),
                                    );
                                }
                                "intersection" => {
                                    let op2 = self.convert_set_term(op2.clone(), bound_variable)?;
                                    let op1 = self.convert_set_term(op1.clone(), bound_variable)?;
                                    return Some(
                                        ast::Set::intersect(self.ctx, &[&op1, &op2]).into(),
                                    );
                                }
                                "setminus" => {
                                    let op2 = self
                                        .convert_set_term(op2.clone(), bound_variable)?
                                        .complement();
                                    let op1 = self.convert_set_term(op1.clone(), bound_variable)?;
                                    return Some(
                                        ast::Set::intersect(self.ctx, &[&op1, &op2]).into(),
                                    );
                                }
                                "plus" => {
                                    if detect_z_ty(op) {
                                        let op2 =
                                            self.convert_int_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_int_term(op1.clone(), bound_variable)?;
                                        return Some((op1 + op2).into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 =
                                            self.convert_real_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_real_term(op1.clone(), bound_variable)?;
                                        return Some((op1 + op2).into());
                                    }
                                    if let Some(elem_ty) = detect_list_ty(op) {
                                        if detect_char_ty(&elem_ty) {
                                            let a = self
                                                .convert_string_term(op1.clone(), bound_variable)?;
                                            let b = self
                                                .convert_string_term(op2.clone(), bound_variable)?;
                                            return Some(
                                                ast::String::concat(self.ctx, &[&a, &b]).into(),
                                            );
                                        } else {
                                            let a = self
                                                .convert_list_term(op2.clone(), bound_variable)?;
                                            let b = self
                                                .convert_list_term(op1.clone(), bound_variable)?;
                                            return Some(
                                                ast::Seq::concat(self.ctx, &[&a, &b]).into(),
                                            );
                                        }
                                    }
                                }
                                "minus" => {
                                    if detect_z_ty(op) {
                                        let op2 =
                                            self.convert_int_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_int_term(op1.clone(), bound_variable)?;
                                        return Some((op1 - op2).into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 =
                                            self.convert_real_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_real_term(op1.clone(), bound_variable)?;
                                        return Some((op1 - op2).into());
                                    }
                                }
                                "mult" => {
                                    if detect_z_ty(op) {
                                        let op2 =
                                            self.convert_int_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_int_term(op1.clone(), bound_variable)?;
                                        return Some((op1 * op2).into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 =
                                            self.convert_real_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_real_term(op1.clone(), bound_variable)?;
                                        return Some((op1 * op2).into());
                                    }
                                }
                                "div" => {
                                    if definitely_zero(op2) {
                                        return Some(ast::Real::from_real(self.ctx, 0, 1).into());
                                    }
                                    if detect_z_ty(op) {
                                        let op2 = ast::Real::from_int(
                                            &self.convert_int_term(op2.clone(), bound_variable)?,
                                        );
                                        let op1 = ast::Real::from_int(
                                            &self.convert_int_term(op1.clone(), bound_variable)?,
                                        );
                                        return Some((op1 / op2).into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 =
                                            self.convert_real_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_real_term(op1.clone(), bound_variable)?;
                                        return Some((op1 / op2).into());
                                    }
                                }
                                "pow" => {
                                    if detect_z_ty(op) {
                                        let op2 =
                                            self.convert_int_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_int_term(op1.clone(), bound_variable)?;
                                        let real_pw =
                                            Dynamic::as_real(&op1.power(&op2.clone()).into())?;
                                        return Some(real_pw.to_int().into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 =
                                            self.convert_real_term(op2.clone(), bound_variable)?;
                                        let op1 =
                                            self.convert_real_term(op1.clone(), bound_variable)?;
                                        return Some(op1.power(&op2).into());
                                    }
                                    return None;
                                }
                                "cons" => {
                                    /*if detect_char_ty(op) {
                                        if let Some(s) = detect_string(&t) {
                                            let s =
                                                ast::String::from_str(self.ctx, s.as_str()).ok()?;
                                            return Some(s.into());
                                        }
                                        let s =
                                            self.convert_string_term(op2.clone(), bound_variable)?;
                                        let c =
                                            self.convert_general_term(op1.clone(), bound_variable)?;

                                        return Some(
                                            ast::String::concat(self.ctx, &[&c, &s]).into(),
                                        );
                                    } else {*/
                                    let head =
                                        self.convert_general_term(op1.clone(), bound_variable)?;
                                    let head = ast::Seq::unit(self.ctx, &head);
                                    let tail =
                                        self.convert_list_term(op2.clone(), bound_variable)?;
                                    return Some(
                                        ast::Seq::concat(self.ctx, &[&head, &tail]).into(),
                                    );
                                    //}
                                }
                                // call nth with index 0
                                "head" => {
                                    let ls = self.convert_list_term(op2.clone(), bound_variable)?;
                                    return Some(ls.nth(&ast::Int::from_i64(self.ctx, 0)));
                                }
                                "firstn" => {
                                    let length =
                                        self.convert_int_term(op2.clone(), bound_variable)?;
                                    let ls = self.convert_list_term(op1.clone(), bound_variable)?;
                                    return Some(
                                        ls.subsequance(ast::Int::from_i64(self.ctx, 0), length)
                                            .into(),
                                    );
                                }
                                "skipn" => {
                                    let start =
                                        self.convert_int_term(op2.clone(), bound_variable)?;
                                    let ls = self.convert_list_term(op1.clone(), bound_variable)?;
                                    return Some(
                                        ls.subsequance(start.clone(), ls.length() - start).into(),
                                    );
                                }
                                _ => (),
                            },
                            Term::App { func, op: _ } => {
                                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                                    match unique_name.as_str() {
                                        "if_f" => {
                                            let prop = self.covert_prop_to_z3_bool(
                                                op.clone(),
                                                bound_variable,
                                            )?;
                                            let op1 = self.convert_general_term(
                                                op1.clone(),
                                                bound_variable,
                                            )?;
                                            let op2 = self.convert_general_term(
                                                op2.clone(),
                                                bound_variable,
                                            )?;
                                            return Some(prop.ite(&op1, &op2));
                                        }
                                        "map" => {
                                            if !detect_char_ty(op) {
                                                let ls = self.convert_list_term(
                                                    op2.clone(),
                                                    bound_variable,
                                                )?;
                                                let fun_as_arr =
                                                    self.convert_array_term(op1.clone())?;

                                                //let maped_ls_sort = self.convert_sort(op)?;
                                                let maped_ls_sort =
                                                    Sort::seq(self.ctx, &self.convert_sort(op)?);
                                                let fun = self
                                                    .generate_unknown(
                                                        op1.clone(),
                                                        fun_as_arr.get_sort(),
                                                    )
                                                    .as_array()?;
                                                let from = self
                                                    .generate_unknown(op2.clone(), ls.get_sort())
                                                    .as_seq()?;
                                                let maped_ls = self
                                                    .generate_unknown(t.clone(), maped_ls_sort)
                                                    .as_seq()?;
                                                let prob = self.ctx.from_string(
                                                    "(assert (= (seq.map fun from) to))",
                                                    &[],
                                                    &[],
                                                    &["fun", "from", "to"],
                                                    &[&fun.decl(), &from.decl(), &maped_ls.decl()],
                                                );
                                                self.solver.assert(prob.first().unwrap());
                                                self.solver.assert(&from._eq(&ls));
                                                self.solver.assert(&fun._eq(&fun_as_arr));
                                                return Some(maped_ls.into());
                                            }
                                        }
                                        //nth: forall X, X -> list X -> Z -> X
                                        "nth" => {
                                            let index =
                                                self.convert_int_term(op2.clone(), bound_variable)?;
                                            let ls = self
                                                .convert_list_term(op1.clone(), bound_variable)?;
                                            return Some(ls.nth(&index));
                                        }
                                        _ => (),
                                    }
                                }
                            }
                            _ => (),
                        },
                        Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                            "set_singleton" => {
                                return Some(
                                    ast::Set::empty(self.ctx, &self.convert_sort(op1)?)
                                        .add(
                                            &self.convert_general_term(
                                                op2.clone(),
                                                &bound_variable,
                                            )?,
                                        )
                                        .into(),
                                );
                            }
                            "mod_of" => {
                                let op2 = self.convert_int_term(op2.clone(), bound_variable)?;
                                let op1 = self.convert_int_term(op1.clone(), bound_variable)?;
                                return Some((op1.rem(&op2)).into());
                            }
                            /*      "pow" => {
                                let op2 = self.convert_int_term(op2.clone())?;
                                let op1 = self.convert_int_term(op1.clone())?;
                                return Some(
                                    ast::Real::try_from(ast::Dynamic::from(op1.power(&op2)))
                                        .unwrap()
                                        .to_int()
                                        .into(),
                                );
                            }*/
                            "neg" => {
                                if detect_z_ty(op1) {
                                    let op = self.convert_int_term(op2.clone(), bound_variable)?;
                                    return Some((-op).into());
                                } else if detect_r_ty(op1) {
                                    let op = self.convert_real_term(op2.clone(), bound_variable)?;
                                    return Some((-op).into());
                                }
                            }
                            "len1" => {
                                if detect_z_ty(op1) {
                                    let a = self.convert_int_term(op2.clone(), bound_variable)?;
                                    return Some(
                                        a.clone()
                                            .ge(&ast::Int::from_u64(self.ctx, 0))
                                            .ite(&a.clone(), &(-a))
                                            .into(),
                                    );
                                } else if detect_list_ty(op1).is_some() {
                                    let l = self.convert_list_term(op2.clone(), bound_variable)?;
                                    return Some(l.length().into());
                                }
                            }
                            "Eucli" => {
                                let op = self.convert_general_term(
                                    app_ref!(
                                        abs(),
                                        app_ref!(app_ref!(app_ref!(minus(), r()), op1), op2)
                                    ),
                                    &bound_variable,
                                )?;
                                return Some(op);
                            }
                            _ => (),
                            //     "minus" => minus(
                            //         term_ref_to_arith(op1.clone(), arena),
                            //         term_ref_to_arith(op2.clone(), arena),
                            //         arena,
                            //     ),
                            //     "pow" => pow_to_arith(op1.clone(), op2.clone(), arena),
                            //     "len1" => return len1_to_arith(op1.clone(), op2.clone(), arena),
                            //     _ => atom_normalizer(t),
                        },
                        _ => (),
                    },
                    _ => (),
                }
                /*if let Some(func) = self.convert_array_term(func.clone()) {
                    let index = self.convert_general_term(op2.clone(), bound_variable)?;
                    dbg!(func.clone());
                    let result = panic::catch_unwind(|| func.select(&index));
                    match result {
                        Ok(res) => return Some(res),
                        Err(_) => print!("ehahd"),
                    }
                }*/
            }
            Term::Wild { .. } => unreachable!(),
        }
        if self.is_calculator {
            return None;
        }
        let ty = type_of(t.clone()).unwrap();
        let sort = self.convert_sort(&ty)?;
        dbg!(sort.clone());
        Some(self.generate_unknown(t, sort))
    }

    fn convert_sort(&self, t: &Term) -> Option<Sort<'a>> {
        if detect_z_ty(t) {
            return Some(Sort::int(self.ctx));
        }
        if detect_r_ty(t) {
            return Some(Sort::real(self.ctx));
        }
        if detect_char_ty(t) {
            let c = ast::String::from_str(self.ctx, "a").unwrap();
            let c = unsafe { ast::Seq::wrap(self.ctx, c.get_z3_ast()) };
            let c = c.nth(&ast::Int::from_i64(self.ctx, 0));
            return Some(c.get_sort());
        }
        if let Some(elt) = detect_list_ty(t) {
            if detect_char_ty(&elt) {
                return Some(Sort::string(self.ctx));
            } else {
                let elt = self.convert_sort(&elt)?;
                return Some(Sort::seq(self.ctx, &elt));
            }
        }
        if let Some(ty) = detect_set_ty(t) {
            let sort = self.convert_sort(&ty)?;
            return Some(Sort::set(self.ctx, &sort));
        }
        if let Term::Axiom { ty, unique_name } = t {
            assert!(matches!(ty.as_ref(), Term::Universe { .. }));
            return Some(Sort::uninterpreted(
                self.ctx,
                z3::Symbol::String(unique_name.to_string()),
            ));
        }
        if let Term::Forall(a) = t {
            let domain = self.convert_sort(&a.var_ty)?;
            let range = self.convert_sort(&a.body)?;
            return Some(Sort::array(self.ctx, &domain, &range));
        }
        let ty = type_of(Rc::new(t.clone())).ok()?;
        if let Term::Universe { index } = ty.as_ref() {
            if *index == 0 {
                return Some(Sort::uninterpreted(
                    self.ctx,
                    z3::Symbol::String(format!("{:?}", t)),
                ));
            }
        }
        None
    }

    fn get_finite_for_sort(&self, ty: TermRef) -> Option<FuncDecl<'a>> {
        let sort_elem = self.convert_sort(&ty)?;
        let sort = Sort::set(self.ctx, &sort_elem);
        let id = lookup_in_cell_hashmap(&self.unknowns.0, ty);
        let r = FuncDecl::new(
            self.ctx,
            format!("$finite{id}"),
            &[&sort],
            &Sort::bool(self.ctx),
        );
        if !check_exists_and_insert(&self.finite_axioms, id) {
            self.solver.assert(
                &r.apply(&[&Set::empty(self.ctx, &sort_elem)])
                    .try_into()
                    .unwrap(),
            );
            let elem = Dynamic::new_const(self.ctx, "e", &sort_elem);
            let set1: Set = Dynamic::new_const(self.ctx, "s1", &sort)
                .try_into()
                .unwrap();
            let set2: Set = Dynamic::new_const(self.ctx, "s2", &sort)
                .try_into()
                .unwrap();
            let s1f: Bool = r.apply(&[&set1]).try_into().unwrap();
            let s2f: Bool = r.apply(&[&set2]).try_into().unwrap();
            self.solver.assert(&forall_const(
                self.ctx,
                &[&elem, &set1],
                &[],
                &s1f.implies(&r.apply(&[&set1.add(&elem)]).try_into().unwrap()),
            ));
            self.solver.assert(&forall_const(
                self.ctx,
                &[&set2, &set1],
                &[],
                &s1f.implies(
                    &s2f.implies(
                        &r.apply(&[&Set::set_union(self.ctx, &[&set1, &set2])])
                            .try_into()
                            .unwrap(),
                    ),
                ),
            ));
            self.solver.assert(&forall_const(
                self.ctx,
                &[&set2, &set1],
                &[],
                &s1f.implies(&set2.set_subset(&set1).implies(&s2f)),
            ));
        }
        Some(r)
    }
}

fn definitely_zero(op2: &Term) -> bool {
    match op2 {
        Term::Number { value } => value == &0.into(),
        Term::NumberR { value, .. } => value == &0.into(),
        _ => false,
    }
}

pub static Z3_TIMEOUT: Mutex<Duration> = Mutex::new(Duration::from_millis(2000));

fn z3_can_solve(frame: Frame) -> bool {
    let cfg = &Config::new();
    let ctx = &Context::new(cfg);
    let solver = Tactic::new(ctx, "default")
        .try_for(*Z3_TIMEOUT.lock().unwrap())
        .solver();
    let z3manager = Z3Manager {
        ctx,
        unknowns: Z3Names::default(),
        finite_axioms: Cell::default(),
        solver,
        is_calculator: frame.engine.params.get("auto_level") == Some(&"calculator".to_string()),
    };
    for hyp in frame.hyps {
        println!("{:?}", &hyp.ty.clone());
        let Some(b) = z3manager.covert_prop_to_z3_bool(hyp.ty, &[]) else {
            continue;
        };
        z3manager.solver.assert(&b);
    }
    if let Some(b) = z3manager.covert_prop_to_z3_bool(frame.goal, &[]) {
        z3manager.solver.assert(&b.not());
    }

    dbg!(&z3manager.solver);
    z3manager.solver.check() == SatResult::Unsat
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nz3");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "z3");
    }

    #[test]
    fn simple() {
        success("False -> True");
        success("False -> 2 = 5");
        success("2 = 5 -> False");
        success("2. = 5. -> False");
        success("1 / 2 = 0.5");
        fail("True -> 2 = 5");
        success("1. + 2. = 3.");
        success("0.5 + 0.5 = 1.");
        success("1 / 2 + 0.5 = 1.");
        success("0.5 * 0.5 = 0.25");
        fail("1. + 2. = 4.");
        success("|-2| > 0");
        fail("∀ a: A, ~ a ∈ S -> |S ∪ {a}| = 3 -> |S| = 2");
    }

    #[test]
    fn simple_variables() {
        success("∀ x: ℝ, x = 3. -> x < 3.01");
    }

    #[test]
    fn modulo_test() {
        success("6 | 24");
        // z3 can't prove that, we just want to check it doesn't hang
        fail("∀ x y z, x > 0 -> y > 0 -> z > 0 -> x | y -> y | z -> x | z");
    }

    #[test]
    fn success_unused_var() {
        success("forall x c a: ℤ, 2 * c = a -> ~ 2 * x = 1");
    }

    #[test]
    fn multiple_theories() {
        success("∀ x: ℤ, x ∈ {2} -> x + x = 4");
        //    success("∀ k p: ℤ, ~ 4 * k * + 4 * k + 1 = 2 * p");
    }

    #[test]
    fn pow_rules() {
        success("∀ x y: ℤ, 2 ^ (x + y) = 2^x * 2^y");
        success("2 ^ 3 = 8");
        success("sqrt 8. = 2. * sqrt 2.");
        success("∀ a b: ℤ, ~ b = 0 -> (a / b) ^ 2. = (a * a) / (b * b)");
        // success("∀ x: ℤ, x > 0 -> 2 ^ (x + x) = 2 ^ x * 2 ^ x -> (∀ y: ℤ, y > 0 -> 2 ^ (y + y) = 2 ^ y * 2 ^ y)");
        // success("∀ x: ℤ, x > 0 -> 2 ^ (x + x) = 2 ^ x * 2 ^ x");
    }

    #[test]
    fn z3_panic1() {
        fail("∀ f: ℝ -> ℝ, f 2. = 3. -> False");
    }
    #[test]
    fn z3_simple_can_solve() {
        success("∀ x y: ℤ, x mod y = x - y mod y");
        success("∀ k p: ℤ, ~ 2 * (2 * k ^ 2 + 2 * k) + 1 = 2 * p");
        success("∀ k: ℤ, True");
        success("∀ p q: ℤ, ~ 2 * gcd p q = 1");
        success("∀ p q: ℤ, ~ p = q -> if_f (p = q) 1 0 = 0");
    }
    #[test]
    fn abs_test() {
        success("abs (2. - 4.) = 2.");
        success("Eucli 2. 4. = 2.");
        success("false");
    }

    #[test]
    fn string_test() {
        success(r#""sa" + "lam" + " ali" = "salam ali""#);
    }

    #[test]
    fn list_calculate() {
        success("|[2, 3, 4]| = 3");
        success(r#"map (λ x, if_f (x = 2) 2 4) [2, 3] = [2, 4]"#);
        fail("(λ x y: ℤ, if_f (x = 2) y (2 * y)) 2 3 = 3");
        fail("∀ y: list ℤ, ∀ x: ℤ, ∀ f: ℤ → ℤ, map f (x :: y) = f x :: map f y");
        success("∀ d: ℤ, ∀ n: list ℤ, 0 < d ∧ d < 10 → ~ head 0 (d :: n) = 0");
        fail("∀ X Y: U, ∀ f: X -> Y, ∀ p q: X, f p = f q");
        success("2 in 3::[4, 2]");
        success("firstn [2, 3, 4] 2 = [2, 3]");
        success("skipn [2, 3, 4] 2 = [4]");
        fail("∀ T: U, ∀ l: list T, ∀ i: ℤ, 0 < i -> i < |l| -> l = firstn l i + skipn l i");
    }
    #[test]
    fn list_not_solve() {
        success("∀ n: ℤ, 0 < n → ∀ x y: list char, (0, 0) :: list_of_fun (2 * n) (λ i: ℤ, (cnt '(' (firstn x i), cnt ')' (firstn x i))) = (0, 0) :: list_of_fun (2 * n) (λ i: ℤ, (cnt '(' (firstn y i), cnt ')' (firstn y i))) → list_of_fun (2 * n) (λ i: ℤ, (cnt '(' (firstn x i), cnt ')' (firstn x i))) = list_of_fun (2 * n) (λ i: ℤ, (cnt '(' (firstn y i), cnt ')' (firstn y i)))");
    }
    #[test]
    fn if_f_not_solve() {
        success("∀ X: Universe → Universe, ∀ A B: Universe, ∀ s: X A, ∀ m: X B, ∀ t: set (X A), s ∈ t → ∀ n: X B, if_f (s ∈ t) m n = m");
    }
    #[test]
    fn char_parse() {
        success(r#" ∀ s, 'a'::s = "a" + s "#);
        success(r#"nth '*' "aa" 0 = 'a'"#);
        fail(r#"nth '*' "aa" 0 ∈ member_set "a""#);
    }
}
