use z3::{
    ast::{self, Ast},
    Config, Context, SatResult, Solver, Sort,
};

use crate::{
    brain::{
        detect::{detect_r_ty, detect_set_ty, detect_z_ty},
        remove_unused_var, Abstraction, Term, TermRef,
    },
    interactive::Frame,
};

use super::{Error::CanNotSolve, Result};

pub fn z3_auto(frame: Frame) -> Result<Vec<Frame>> {
    if z3_can_solve(frame) {
        Ok(vec![])
    } else {
        Err(CanNotSolve("z3"))
    }
}

struct Z3Manager<'a> {
    ctx: &'a Context,
}

impl<'a> Z3Manager<'a> {
    fn covert_prop_to_z3_bool(&self, t: TermRef) -> Option<ast::Bool<'a>> {
        if let Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) = t.as_ref()
        {
            if let Some(body) = remove_unused_var(body.clone()) {
                let op1 = self.covert_prop_to_z3_bool(var_ty.clone())?;
                let op2 = self.covert_prop_to_z3_bool(body)?;
                return Some(op1.implies(&op2));
            }
        }
        if let Term::App { func, op: op2 } = t.as_ref() {
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "and" || unique_name == "or" {
                        let op1 = &self.covert_prop_to_z3_bool(op1.clone())?;
                        let op2 = &self.covert_prop_to_z3_bool(op2.clone())?;
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
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::App { func, op: ty } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        match unique_name.as_str() {
                            "eq" => {
                                let op1 = self.convert_general_term(op1)?;
                                let op2 = self.convert_general_term(op2)?;
                                return Some(op1._safe_eq(&op2).unwrap());
                            }
                            "inset" => {
                                let op2 = self.convert_set_term(op2)?;
                                let op1 = self.convert_general_term(op1)?;
                                return Some(op2.member(&op1));
                            }
                            "included" => {
                                let op2 = self.convert_set_term(op2)?;
                                let op1 = self.convert_set_term(op1)?;
                                return Some(op1.set_subset(&op2));
                            }
                            "lt" => {
                                if detect_z_ty(ty) {
                                    let op1 = self.convert_int_term(op1)?;
                                    let op2 = self.convert_int_term(op2)?;
                                    return Some(op1.lt(&op2));
                                }
                                if detect_r_ty(ty) {
                                    let op1 = self.convert_real_term(op1)?;
                                    let op2 = self.convert_real_term(op2)?;
                                    return Some(op1.lt(&op2));
                                }
                            }
                            _ => (),
                        }
                    }
                }
            }
        }
        None
    }

    fn convert_int_term(&self, t: &Term) -> Option<ast::Int<'a>> {
        Some(
            self.convert_general_term(t)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    fn convert_set_term(&self, t: &Term) -> Option<ast::Set<'a>> {
        Some(
            self.convert_general_term(t)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    fn convert_real_term(&self, t: &Term) -> Option<ast::Real<'a>> {
        Some(
            self.convert_general_term(t)?
                .try_into()
                .expect("mismatched type"),
        )
    }

    #[allow(clippy::single_match)]
    fn convert_general_term(&self, t: &Term) -> Option<ast::Dynamic<'a>> {
        match t {
            Term::Axiom { ty, unique_name } => {
                if detect_z_ty(ty) {
                    return Some(ast::Int::new_const(self.ctx, unique_name.as_str()).into());
                }
                if detect_r_ty(ty) {
                    return Some(ast::Real::new_const(self.ctx, unique_name.as_str()).into());
                }
                let sort = self.convert_sort(ty)?;
                Some(ast::Dynamic::new_const(
                    self.ctx,
                    unique_name.as_str(),
                    &sort,
                ))
            }
            Term::Universe { .. } => None,
            Term::Forall(_) => todo!(),
            Term::Fun(_) => todo!(),
            Term::Var { .. } => unreachable!(),
            Term::Number { value } => {
                let x = ast::Int::from_i64(self.ctx, value.try_into().ok()?);
                Some(x.into())
            }
            Term::NumberR { value, point } => {
                let x = ast::Real::from_real(
                    self.ctx,
                    value.try_into().ok()?,
                    (*point < 10).then(|| 10_i32.pow(*point as u32))?,
                );
                Some(x.into())
            }
            Term::App { func, op: op2 } => {
                match func.as_ref() {
                    Term::Axiom { unique_name, .. } => {
                        if unique_name == "set_empty" {
                            return Some(
                                ast::Set::empty(self.ctx, &self.convert_sort(op2)?).into(),
                            );
                        }
                    }
                    Term::App { func, op: op1 } => match func.as_ref() {
                        Term::Axiom { unique_name, .. } => {
                            if unique_name == "set_singleton" {
                                return Some(
                                    ast::Set::empty(self.ctx, &self.convert_sort(op1)?)
                                        .add(&self.convert_general_term(op2)?)
                                        .into(),
                                );
                            }
                        }
                        Term::App { func, op } => match func.as_ref() {
                            Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                                // "sigma" => {
                                //     return sigma_to_arith(op.clone(), op1.clone(), op2.clone(), arena);
                                // }
                                // "cnt" => {
                                //     return cnt_to_arith(op.clone(), op1.clone(), op2.clone(), arena);
                                // }
                                "union" => {
                                    let op2 = self.convert_set_term(op2)?;
                                    let op1 = self.convert_set_term(op1)?;
                                    return Some(
                                        ast::Set::set_union(self.ctx, &[&op1, &op2]).into(),
                                    );
                                }
                                "intersection" => {
                                    let op2 = self.convert_set_term(op2)?;
                                    let op1 = self.convert_set_term(op1)?;
                                    return Some(
                                        ast::Set::intersect(self.ctx, &[&op1, &op2]).into(),
                                    );
                                }
                                "setminus" => {
                                    let op2 = self.convert_set_term(op2)?.complement();
                                    let op1 = self.convert_set_term(op1)?;
                                    return Some(
                                        ast::Set::intersect(self.ctx, &[&op1, &op2]).into(),
                                    );
                                }
                                "plus" => {
                                    if detect_z_ty(op) {
                                        let op2 = self.convert_int_term(op2)?;
                                        let op1 = self.convert_int_term(op1)?;
                                        return Some((op1 + op2).into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 = self.convert_real_term(op2)?;
                                        let op1 = self.convert_real_term(op1)?;
                                        return Some((op1 + op2).into());
                                    }
                                    return None;
                                }
                                "mult" => {
                                    if detect_z_ty(op) {
                                        let op2 = self.convert_int_term(op2)?;
                                        let op1 = self.convert_int_term(op1)?;
                                        return Some((op1 * op2).into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 = self.convert_real_term(op2)?;
                                        let op1 = self.convert_real_term(op1)?;
                                        return Some((op1 * op2).into());
                                    }
                                    return None;
                                }
                                "div" => {
                                    if definitely_zero(op2) {
                                        return Some(ast::Real::from_real(self.ctx, 0, 1).into());
                                    }
                                    if detect_z_ty(op) {
                                        let op2 = ast::Real::from_int(&self.convert_int_term(op2)?);
                                        let op1 = ast::Real::from_int(&self.convert_int_term(op1)?);
                                        return Some((op1 / op2).into());
                                    }
                                    if detect_r_ty(op) {
                                        let op2 = self.convert_real_term(op2)?;
                                        let op1 = self.convert_real_term(op1)?;
                                        return Some((op1 / op2).into());
                                    }
                                    return None;
                                }
                                _ => (),
                            },
                            _ => (),
                        },
                        // Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                        //     "minus" => minus(
                        //         term_ref_to_arith(op1.clone(), arena),
                        //         term_ref_to_arith(op2.clone(), arena),
                        //         arena,
                        //     ),
                        //     "pow" => pow_to_arith(op1.clone(), op2.clone(), arena),
                        //     "len1" => return len1_to_arith(op1.clone(), op2.clone(), arena),
                        //     _ => atom_normalizer(t),
                        // },
                        _ => (),
                    },
                    _ => (),
                }
                None
            }
            Term::Wild { .. } => unreachable!(),
        }
    }

    fn convert_sort(&self, t: &Term) -> Option<Sort<'a>> {
        if detect_z_ty(t) {
            return Some(Sort::int(self.ctx));
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

fn z3_can_solve(frame: Frame) -> bool {
    let cfg = &Config::new();
    let ctx = &Context::new(cfg);
    let z3manager = Z3Manager { ctx };
    let solver = Solver::new(ctx);
    for hyp in frame.hyps {
        let Some(b) = z3manager.covert_prop_to_z3_bool(hyp.ty) else { continue; };
        solver.assert(&b);
    }
    if let Some(b) = z3manager.covert_prop_to_z3_bool(frame.goal) {
        solver.assert(&b.not());
    }
    dbg!(&solver);
    solver.check() == SatResult::Unsat
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
    }

    #[test]
    fn simple_variables() {
        success("∀ x: ℝ, x = 3. -> x < 3.01");
    }
}
