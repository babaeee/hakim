use std::{
    cell::Cell,
    collections::HashSet,
    fmt::format,
    ops::{Not, Shl},
    rc::Rc,
    sync::Mutex,
    time::Duration,
};

use im::HashMap;

use smt2::*;

use crate::{
    analysis::arith::SigmaSimplifier,
    app_ref,
    brain::{
        detect::{
            detect_char, detect_char_ty, detect_list_ty, detect_r_ty, detect_set_ty, detect_z_ty,
        },
        remove_unused_var, type_of, Abstraction, Term, TermRef,
    },
    interactive::Frame,
    library::prelude::{abs, minus, r, to_universe},
};

pub fn z3_auto(frame: Frame) -> String {
    z3_can_solve(frame)
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

fn check_exists(x: &Cell<HashMap<TermRef, usize>>, key: TermRef) -> bool {
    let h = x.take();
    let ex = h.contains_key(key.as_ref());
    x.set(h);
    ex
}

fn check_exists_and_insert(x: &Cell<HashSet<usize>>, key: usize) -> bool {
    let mut h = x.take();
    let ex = h.insert(key);
    x.set(h);
    !ex
}

struct Z3Manager {
    smt_ctx: Smt2Context,
    unknowns: Z3Names,
    finite_axioms: Cell<HashSet<usize>>,
    is_calculator: bool,
}

impl<'a> SigmaSimplifier for &Z3Manager {
    type T = String;

    fn handle_sigma_atom(self, r: TermRef, f: TermRef) -> Self::T {
        todo!()
        /*       let id = lookup_in_cell_hashmap(&self.unknowns.0, f);
        let f = FuncDecl::new(
            self.ctx,
            format!("$sigma{id}"),
            &[&Sort::int(self.ctx)],
            &Sort::int(self.ctx),
        );
        f.apply(&[&self.handle_term(r)]).try_into().unwrap()*/
    }

    fn minus(self, x: Self::T, y: Self::T) -> Self::T {
        todo!();
        //     x - y
    }

    fn mult(self, x: Self::T, y: Self::T) -> Self::T {
        todo!();
        //x * y
    }

    fn plus(self, x: Self::T, y: Self::T) -> Self::T {
        todo!();
        //    x + y
    }

    fn handle_term(self, t: TermRef) -> Self::T {
        todo!()
        //        self.convert_int_term(t, &[]).unwrap()
    }
}

impl<'a> Z3Manager {
    fn covert_prop_to_z3_bool(
        &mut self,
        t: TermRef,
        bound_variable: &[String],
    ) -> Option<smt2::Term> {
        if let Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) = t.as_ref()
        {
            if let Some(body) = remove_unused_var(body.clone()) {
                let op1 = self.covert_prop_to_z3_bool(var_ty.clone(), bound_variable)?;
                let op2 = self.covert_prop_to_z3_bool(body, bound_variable)?;
                return Some(op1.implies(op2));
            }
        }
        if let Term::App { func, op: op2 } = t.as_ref() {
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "and" || unique_name == "or" {
                        let op1 = &self.covert_prop_to_z3_bool(op1.clone(), bound_variable)?;
                        let op2 = &self.covert_prop_to_z3_bool(op2.clone(), bound_variable)?;
                        return Some(match unique_name.as_str() {
                            "and" => smt2::Term::land(op1.clone(), op2.clone()),
                            "or" => smt2::Term::lor(op1.clone(), op2.clone()),
                            _ => unreachable!(),
                        });
                    }
                }
            }
        }
        if let Term::Axiom { unique_name, .. } = t.as_ref() {
            if unique_name == "False" || unique_name == "True" {
                let t = match unique_name.as_str() {
                    "True" => true,
                    "False" => false,
                    _ => unreachable!(),
                };
                return Some(smt2::Term::Binary(t));
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
                                return Some(smt2::Term::bveq(op1, op2));
                            }
                            "inset" => {
                                let op2 = self.convert_general_term(op2, bound_variable)?;
                                let op1 = self.convert_general_term(op1, bound_variable)?;
                                return Some(smt2::Term::select(op2, vec![op1]));
                            }
                            "inlist" => {
                                let ls = self.convert_general_term(op2, bound_variable)?;
                                let elem = self.convert_general_term(op1, &bound_variable)?;
                                return Some(smt2::Term::Identifier(format!(
                                    "(seq.contains {ls} (seq.unit {elem}))"
                                )));
                            }
                            "included" => {
                                let op2 = self.convert_general_term(op2, bound_variable)?;
                                let op1 = self.convert_general_term(op1, bound_variable)?;
                                return Some(smt2::Term::Identifier(format!(
                                    "(subset {op1} {op2})"
                                )));
                            }
                            "lt" => {
                                if detect_z_ty(ty) || detect_r_ty(ty) {
                                    let op1 = self.convert_general_term(op1, bound_variable)?;
                                    let op2 = self.convert_general_term(op2, bound_variable)?;
                                    return Some(smt2::Term::Identifier(format!(
                                        "(< {op1} {op2})"
                                    )));
                                }
                            }
                            _ => (),
                        }
                    }
                }
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    match unique_name.as_str() {
                        "divide" => {
                            let op1 = self.convert_general_term(op1, bound_variable)?;
                            let op2 = self.convert_general_term(op2, bound_variable)?;
                            return Some(smt2::Term::Identifier(format!(
                                "(= (rem {op2} {op1}) 0)"
                            )));
                        }
                        "finite" => {
                            //   let x = self.get_finite_for_sort(op1)?;
                            //   let set = self.convert_general_term(op2, bound_variable)?;
                            //  return Some(x.apply(&[&set]).try_into().unwrap());
                            return None;
                        }
                        _ => (),
                    }
                }
            }
        }
        Some(self.generate_unknown(t, "Bool".to_string()).unwrap())
    }

    fn generate_unknown(&mut self, key: TermRef, sort: String) -> Option<smt2::Term> {
        let id = if !check_exists(&self.unknowns.0, key.clone()) {
            let id = lookup_in_cell_hashmap(&self.unknowns.0, key);
            self.smt_ctx
                .variable(smt2::VarDecl::new(format!("$x{id}"), sort));
            id
        } else {
            lookup_in_cell_hashmap(&self.unknowns.0, key)
        };
        return Some(smt2::Term::Identifier(format!("$x{id}")));
    }

    fn convert_array_term(&mut self, t: TermRef) -> Option<String> {
        let mut bound_variable = vec![];
        // let mut names = vec![];
        let mut term_body = t;
        while let Term::Fun(a) = term_body.as_ref() {
            let sort = self.convert_sort(&a.var_ty)?;
            bound_variable.push(smt2::SortedVar::new(a.hint_name.clone().expect("_"), sort));
            term_body = a.body.clone();
        }
        let names: Vec<String> = bound_variable.iter().map(|var| var.ident.clone()).collect();
        let body = self.convert_general_term(term_body, names.as_slice())?;
        if bound_variable.is_empty() {
            return Some(format!("{body}"));
        }
        let t = smt2::Term::lambda(bound_variable, body);
        return Some(format!("{t}"));
    }

    #[allow(clippy::single_match)]
    fn convert_general_term(
        &mut self,
        t: TermRef,
        bound_variable: &[String],
    ) -> Option<smt2::Term> {
        match t.as_ref() {
            Term::Axiom { ty, unique_name } => {
                if self.is_calculator {
                    return None;
                }
                if check_exists(&self.unknowns.0, t.clone()) {
                    return Some(smt2::Term::Identifier(unique_name.clone()));
                }
                let sort = self.convert_sort(ty)?;
                self.smt_ctx
                    .variable(VarDecl::new(unique_name.clone(), sort));
                lookup_in_cell_hashmap(&self.unknowns.0, t.clone());
                return Some(smt2::Term::Identifier(unique_name.clone()));
            }
            Term::Universe { .. } => (),
            Term::Forall(_) => todo!(),
            Term::Fun(_) => (),
            Term::Var { index } => {
                let name = bound_variable.get(*index)?;
                return Some(smt2::Term::Identifier(name.clone()));
            }
            Term::Number { value } => {
                return Some(smt2::Term::Identifier(value.to_string()));
            }
            Term::NumberR { value, point } => {
                let mut value = value.to_string();
                if value.len() < *point {
                    let mut zeros: String =
                        std::iter::repeat('0').take(point - value.len()).collect();
                    zeros.insert(0, '.');
                    value.insert_str(0, zeros.as_str())
                } else {
                    value.insert(value.len() - point, '.');
                }
                return Some(smt2::Term::Identifier(value));
            }
            Term::App { func, op: op2 } => {
                let op2_t = self
                    .convert_general_term(op2.clone(), bound_variable)
                    .unwrap_or(smt2::Term::Identifier("".to_string()));
                match func.as_ref() {
                    Term::Axiom { unique_name, .. } => {
                        if unique_name == "set_empty" {
                            let sort = self.convert_sort(op2)?;
                            return Some(smt2::Term::Identifier(format!(
                                "((as const (Array {sort} Bool)) false)"
                            )));
                        }
                        if unique_name == "nil" {
                            if detect_char_ty(op2) {
                                let nil = "";
                                return Some(smt2::Term::Identifier(nil.to_string()));
                            } else {
                                let sort = self.convert_sort(op2)?;
                                return Some(smt2::Term::Identifier(format!(
                                    "(as seq.empty (Seq {sort}))"
                                )));
                            }
                        }
                        if unique_name == "chr" {
                            let c = detect_char(&t)?;
                            let unicode = format!("{:X}", (c as u8));
                            return Some(smt2::Term::Identifier(format!("#x{unicode}")));
                        }
                        if unique_name == "sqrt" {
                            return Some(smt2::Term::Identifier(format!("(^ {op2_t} 0.5")));
                        }
                        if unique_name == "abs" {
                            return Some(smt2::Term::Identifier(format!(
                                "(ite (>= {op2_t} 0) {op2_t} (- {op2_t}))"
                            )));
                        }
                    }
                    Term::App { func, op: op1 } => {
                        let op1_t = self
                            .convert_general_term(op1.clone(), bound_variable)
                            .unwrap_or(smt2::Term::Identifier("".to_string()));
                        match func.as_ref() {
                            Term::App { func, op } => match func.as_ref() {
                                Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                                    "sigma" => {
                                        /* return Some(
                                            sigma_to_arith::<_, BigInt>(
                                                op.clone(),
                                                op1.clone(),
                                                op2.clone(),
                                                self,
                                            )
                                            .into(),
                                        );*/
                                    }
                                    // "cnt" => {
                                    //     return cnt_to_arith(op.clone(), op1.clone(), op2.clone(), arena);
                                    // }
                                    "union" => {
                                        let sort = self.convert_sort(op)?;
                                        return Some(smt2::Term::Identifier(format!(
                                            "((as union (Array {sort} Bool)) {op1_t} {op2_t})"
                                        )));
                                    }
                                    "intersection" => {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(intersection {op1_t} {op2_t})"
                                        )));
                                    }
                                    "setminus" => {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(setminus {op1_t} {op2_t})"
                                        )));
                                    }
                                    "plus" => {
                                        let add = if detect_z_ty(op) || detect_r_ty(op) {
                                            "+"
                                        } else if let Some(elem_ty) = detect_list_ty(op) {
                                            if detect_char_ty(&elem_ty) {
                                                "str.++"
                                            } else {
                                                "seq.++"
                                            }
                                        } else {
                                            ""
                                        };
                                        return Some(smt2::Term::Identifier(format!(
                                            "({add} {op1_t} {op2_t})"
                                        )));
                                    }
                                    "minus" => {
                                        if detect_z_ty(op) || detect_r_ty(op) {
                                            return Some(smt2::Term::Identifier(format!(
                                                "(- {op1_t} {op2_t})"
                                            )));
                                        }
                                    }
                                    "mult" => {
                                        if detect_z_ty(op) || detect_r_ty(op) {
                                            return Some(smt2::Term::Identifier(format!(
                                                "(* {op1_t} {op2_t})"
                                            )));
                                        }
                                    }
                                    "div" => {
                                        if definitely_zero(op2) {
                                            return Some(smt2::Term::Identifier("0.0".to_string()));
                                        }
                                        if detect_z_ty(op) || detect_r_ty(op) {
                                            return Some(smt2::Term::Identifier(format!(
                                                "(/ {op1_t} {op2_t})"
                                            )));
                                        }
                                    }
                                    "pow" => {
                                        if detect_z_ty(op) || detect_r_ty(op) {
                                            let mut real_pw = format!("(^ {op1_t} {op2_t})");
                                            if detect_z_ty(op) {
                                                real_pw = format!("(to_int {real_pw})");
                                            }
                                            return Some(smt2::Term::Identifier(real_pw));
                                        }
                                        return None;
                                    }
                                    "cons" => {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(seq.++ (seq.unit {op1_t}) {op2_t})"
                                        )));
                                    }
                                    // call nth with index 0
                                    "head" => {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(seq.nth {op2_t} 0)"
                                        )));
                                    }
                                    "firstn" => {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(seq.extract {op1_t} 0 {op2_t})"
                                        )));
                                    }
                                    "skipn" => {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(seq.extract {op1_t} {op2_t} (- (seq.len {op1_t}) {op2_t}))"
                                        )));
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
                                                return Some(smt2::Term::Identifier(format!(
                                                    "(ite {prop} {op2_t} {op1_t})"
                                                )));
                                            }
                                            "map" => {
                                                if !detect_char_ty(op) {
                                                    let fun_as_arr =
                                                        self.convert_array_term(op1.clone())?;
                                                    return Some(smt2::Term::Identifier(format!(
                                                        "(seq.map {fun_as_arr} {op2_t})"
                                                    )));
                                                }
                                            }
                                            //nth: forall X, X -> list X -> Z -> X
                                            "nth" => {
                                                return Some(smt2::Term::Identifier(format!(
                                                    "(seq.nth {op1_t} {op2_t})"
                                                )));
                                            }
                                            _ => (),
                                        }
                                    }
                                }
                                _ => (),
                            },
                            Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                                "set_singleton" => {
                                    let sort = self.convert_sort(op1)?;
                                    return Some(smt2::Term::Identifier(format!(
                                        "(store ((as const (Array {sort} Bool)) false) {op2_t} true)"
                                    )));
                                }
                                "mod_of" => {
                                    return Some(smt2::Term::Identifier(format!(
                                        "(rem {op1_t} {op2_t})"
                                    )));
                                }
                                "neg" => {
                                    if detect_z_ty(op1) || detect_r_ty(op1) {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(- {op2_t})"
                                        )));
                                    }
                                }
                                "len1" => {
                                    if detect_z_ty(op1) {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(ite (>= {op2_t} 0) {op2_t} (- {op2_t}))"
                                        )));
                                    } else if detect_list_ty(op1).is_some() {
                                        return Some(smt2::Term::Identifier(format!(
                                            "(seq.len {op2_t})"
                                        )));
                                    }
                                }
                                "Eucli" => {
                                    let op = self.convert_general_term(
                                        app_ref!(
                                            abs(),
                                            app_ref!(app_ref!(app_ref!(minus(), r()), op1), op2)
                                        ),
                                        bound_variable,
                                    )?;
                                    return Some(op);
                                }
                                _ => (),
                                //     "pow" => pow_to_arith(op1.clone(), op2.clone(), arena),
                                //     "len1" => return len1_to_arith(op1.clone(), op2.clone(), arena),
                                //     _ => atom_normalizer(t),
                            },
                            _ => (),
                        }
                    }
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
        if let Term::Universe { .. } = ty.as_ref() {
            return None;
        }
        let sort = self.convert_sort(&ty)?;
        dbg!(sort.clone());
        self.generate_unknown(t, sort)
    }

    fn convert_sort(&mut self, t: &Term) -> Option<String> {
        if detect_z_ty(t) {
            return Some("Int".to_string());
        }
        if detect_r_ty(t) {
            return Some("Real".to_string());
        }
        if detect_char_ty(t) {
            return Some("(_ BitVec 8)".to_string());
        }
        if let Some(elt) = detect_list_ty(t) {
            if detect_char_ty(&elt) {
                return Some("String".to_string());
            } else {
                let elt = self.convert_sort(&elt)?;
                return Some(format!("(Seq {elt})"));
            }
        }
        if let Some(ty) = detect_set_ty(t) {
            let sort = self.convert_sort(&ty)?;
            return Some(format!("(Seq {sort})"));
        }
        /*    if let Term::Axiom { ty, unique_name } = t {
            assert!(matches!(ty.as_ref(), Term::Universe { .. }));

            if check_exists(&self.unknowns.0, TermRef::new(t.clone())) {
                return Some(unique_name.clone());
            }
            let sort = smt2::Sort::Declare(SortDecl::new(unique_name.clone(), 0));
            self.smt_ctx.sort(sort);
            lookup_in_cell_hashmap(&self.unknowns.0, TermRef::new(t.clone()));
            return Some(unique_name.clone());
        }*/
        if let Term::Forall(a) = t {
            let domain = self.convert_sort(&a.var_ty)?;
            let range = self.convert_sort(&a.body)?;

            return Some(format!("(Array {domain} {range})"));
        }
        let ty = type_of(Rc::new(t.clone())).ok()?;
        if let Term::Universe { index } = ty.as_ref() {
            if *index == 0 {
                let key = app_ref!(to_universe(), TermRef::new(t.clone()));
                let sort_name = format!("{:?}", t);
                if check_exists(&self.unknowns.0, key.clone()) {
                    return Some(sort_name);
                }
                let sort = smt2::Sort::Declare(SortDecl::new(sort_name.clone(), 0));
                self.smt_ctx.sort(sort);
                lookup_in_cell_hashmap(&self.unknowns.0, key);
                return Some(sort_name);
            }
        }
        None
    }

    fn get_finite_for_sort(&self, ty: TermRef) -> Option<()> {
        /*   let sort_elem = self.convert_sort(&ty)?;
        let sort = Sort::set(self.ctx, &sort_elem);
        let id: usize = lookup_in_cell_hashmap(&self.unknowns.0, ty);
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
        Some(r)*/
        None
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

fn z3_can_solve(frame: Frame) -> String {
    /*let cfg = &Config::new();
    let ctx = &Context::new(cfg);
    let solver = Tactic::new(ctx, "default")
        .try_for(*Z3_TIMEOUT.lock().unwrap())
        .solver();*/
    let mut z3manager = Z3Manager {
        smt_ctx: Smt2Context::new(),
        unknowns: Z3Names::default(),
        finite_axioms: Cell::default(),
        is_calculator: frame.engine.params.get("auto_level") == Some(&"calculator".to_string()),
    };
    for hyp in frame.hyps {
        println!("{:?}", &hyp.ty.clone());
        let Some(b) = z3manager.covert_prop_to_z3_bool(hyp.ty, &[]) else {
            continue;
        };
        // dbg!(z3manager.smt_ctx.to_code(true));
        z3manager.smt_ctx.assert(b);
    }
    if let Some(b) = z3manager.covert_prop_to_z3_bool(frame.goal, &[]) {
        z3manager.smt_ctx.assert(b.not());
    }
    z3manager.smt_ctx.check_sat();
    let state = z3manager.smt_ctx.to_code(true);
    dbg!(&state);
    state
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{
        run_interactive, run_interactive_to_end, run_interactive_to_fail, EngineLevel,
    };

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nz3");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "z3");
    }

    fn convert_check(term: &str, smt_lib2: &str) {
        let session = run_interactive(term, "intros", EngineLevel::Full);
        let state = session.z3_get_state().unwrap();
        assert_eq!(state, smt_lib2);
    }

    #[test]
    fn check() {
        convert_check("∀ x c: ℤ, 2 * x = c -> False", "(declare-const $x0 Bool)\n(assert $x0)\n(assert $x0)\n(declare-const x Int)\n(declare-const c Int)\n(assert (= (* 2 x) c))\n(assert (not false))\n(check-sat)\n");
        convert_check("∀ x: ℝ, x = 3. -> x > 0.01", "(declare-const $x0 Bool)\n(assert $x0)\n(declare-const x Real)\n(assert (= x 3.))\n(assert (not (< .01 x)))\n(check-sat)\n");
        convert_check("∀ x: ℤ, x ∈ {2} -> x + x = 4", "(declare-const $x0 Bool)\n(assert $x0)\n(declare-const x Int)\n(assert (select (store ((as const (Array Int Bool)) false) 2 true) x))\n(assert (not (= (+ x x) 4)))\n(check-sat)\n");
        convert_check(
            "Eucli 2. 4. = 2.",
            "(assert (not (= (ite (>= (- 2. 4.) 0) (- 2. 4.) (- (- 2. 4.))) 2.)))\n(check-sat)\n",
        );
        convert_check(r#"∀ x: char, 'a' = head '*' "a" "#, "(declare-const $x0 Bool)\n(assert $x0)\n(assert (not (= #x61 (seq.nth (seq.++ (seq.unit #x61) ) 0))))\n(check-sat)\n");
        convert_check(
            "(∃ x, 2 < x) -> (∃ x, 2 < x)",
            "(declare-const $x0 Bool)\n(assert $x0)\n(assert (not $x0))\n(check-sat)\n",
        );
        convert_check(r#""s" + "l" + " a" = "sl a""#, "(assert (not (= (str.++ (str.++ (seq.++ (seq.unit #x73) ) (seq.++ (seq.unit #x6C) )) (seq.++ (seq.unit #x20) (seq.++ (seq.unit #x61) ))) (seq.++ (seq.unit #x73) (seq.++ (seq.unit #x6C) (seq.++ (seq.unit #x20) (seq.++ (seq.unit #x61) )))))))\n(check-sat)\n");
        convert_check(r#"nth '*' "aa" 0 ∈ member_set "a""#, "(declare-const $x0 (Seq (_ BitVec 8)))\n(assert (not (select $x0 (seq.nth (seq.++ (seq.unit #x61) (seq.++ (seq.unit #x61) )) 0))))\n(check-sat)\n");
      //  convert_check(r#"map (λ x, 2*x) [2] = [4]"#, "");
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
