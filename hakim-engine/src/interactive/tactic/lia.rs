use super::Result;
use crate::{
    analysis::{
        arith::{LinearPoly, Poly},
        logic::{LogicArena, LogicBuilder, LogicValue},
    },
    brain::{Term, TermRef},
    interactive::Frame,
};

fn convert_calculator_mode(term: TermRef, arena: LogicArena<'_, Poly>) -> LogicValue<'_, Poly> {
    let r = convert(term, arena);
    fn is_good(x: &LogicValue<'_, Poly>) -> bool {
        match x {
            LogicValue::Exp(_) => false,
            LogicValue::True | LogicValue::False => true,
        }
    }
    if is_good(&r) {
        r
    } else {
        LogicValue::unknown()
    }
}

fn convert(term: TermRef, arena: LogicArena<'_, Poly>) -> LogicValue<'_, Poly> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: _ } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "eq" {
                        let mut d1 = Poly::from_subtract(op2.clone(), op1.clone());
                        if d1.is_zero() {
                            return LogicValue::True;
                        }
                        if d1.variables().is_empty() {
                            return LogicValue::False;
                        }
                        d1.add(1.into());
                        let mut d2 = Poly::from_subtract(op1.clone(), op2.clone());
                        d2.add(1.into());
                        let l1 = LogicValue::from(d1);
                        let l2 = LogicValue::from(d2);
                        return l1.and(l2, arena);
                    }
                }
            }
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "lt" {
                    let d = Poly::from_subtract(op2.clone(), op1.clone());
                    if d.variables().is_empty() {
                        return if *d.constant() > 0i32.into() {
                            LogicValue::True
                        } else {
                            LogicValue::False
                        };
                    }
                    return LogicValue::from(d);
                }
            }
        }
    }
    LogicValue::unknown()
}

fn check_contradiction(polies: &[Poly]) -> bool {
    dbg!(polies);
    let (var_cnt, linear_polies) = LinearPoly::from_slice(polies);
    let mut lower_bounds = vec![None; var_cnt];
    let mut upper_bounds = vec![None; var_cnt];
    for poly in linear_polies {
        match poly.variables() {
            [] => {
                if *poly.constant() <= 0.into() {
                    return true;
                }
            }
            [(a, x)] => {
                let b = -poly.constant();
                // ax > b
                match a.cmp(&0.into()) {
                    std::cmp::Ordering::Less => {
                        // x < b / a
                        let mut ub = &b / a;
                        if b % a == 0.into() {
                            ub -= 1i32;
                        }
                        if let Some(prev_ub) = &upper_bounds[*x] {
                            if ub >= *prev_ub {
                                continue;
                            }
                        }
                        upper_bounds[*x] = Some(ub);
                    }
                    std::cmp::Ordering::Equal => {
                        panic!("Bug in the poly normalizer");
                    }
                    std::cmp::Ordering::Greater => {
                        // x > b / a
                        let lb = b / a + 1i32;
                        if let Some(prev_lb) = &lower_bounds[*x] {
                            if lb <= *prev_lb {
                                continue;
                            }
                        }
                        lower_bounds[*x] = Some(lb);
                    }
                }
            }
            _ => (),
        }
    }
    for (lb, ub) in lower_bounds.iter().zip(upper_bounds.iter()) {
        if let (Some(lb), Some(ub)) = dbg!(lb, ub) {
            if lb > ub {
                return true;
            }
        }
    }
    false
}

fn negator(mut poly: Poly) -> Poly {
    poly.negate();
    poly.add(1.into());
    poly
}

pub fn lia(frame: Frame) -> Result<Vec<Frame>> {
    let is_calculator = frame.engine.params.get("lia") == Some(&"calculator".to_string());
    LogicBuilder::build_tactic(
        "lia",
        frame,
        if is_calculator {
            convert_calculator_mode
        } else {
            convert
        },
        check_contradiction,
        negator,
    )
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail, with_params};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nlia");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "lia");
    }

    #[test]
    fn success_lia_goal() {
        run_interactive_to_end("forall x: ℤ, x < x + 1", "intros\nlia");
    }

    #[test]
    fn success_lia_one_var() {
        run_interactive_to_end(
            "forall x: ℤ, 2 * x < 5 -> 6 * x < 10 + 2 * x",
            "intros\nlia",
        );
    }

    #[test]
    fn lia_and_logic_simple() {
        success("forall x: ℤ, x < 5 ∨ x < 10 -> x < 20");
        fail("forall x: ℤ, x < 5 ∨ x < 100 -> x < 20");
        success("forall x: ℤ, x < 5 ∧ x < 100 -> x < 20");
        success("forall x: ℤ, x < 4 -> x < 20 ∧ (x < 100 ∨ x < 3) ∧ x < 6");
        success("forall x: ℤ, x < 4 -> x < 20 ∧ x < 100 ∨ x < 3 ∧ x < 6");
        fail("forall x: ℤ, x < 4 -> x < 20 ∧ (x < 100 ∨ x < 6) ∧ x < 3");
        success("forall x: ℤ, x = 1 ∨ x = 2 ∨ x = 3 -> x < 4 ∧ 0 < x ∧ (x = 3 ∨ x < 3)");
    }

    #[test]
    fn lia_equality() {
        success("forall x: ℤ, x = 3 ∨ x = 4 -> x < 5");
        success("forall x: ℤ, 3 < x ∧ x < 5 -> x = 4");
        success("forall x: ℤ, 0 < x + 1 -> x = 0 ∨ 0 < x");
        success("forall x: ℤ, 0 < x ∨ 0 = x ∨ x < 0");
        fail("forall x: ℤ, 0 < x ∨ x < 0");
        success("forall x y: ℤ, (x < 10 -> y = 2) -> x = 5 -> y = 2");
        fail("forall x y: ℤ, (x = 5 -> y = 2) -> x < 10 -> y = 2");
    }

    #[test]
    fn success_lia_use_integer() {
        success("forall x: ℤ, 4 < 2 * x -> 5 < 2 * x");
        success("forall x: ℤ, 2 * x < 6 -> 2 * x < 5");
    }

    #[test]
    fn logic_unknown() {
        success("∀ P: U, 2 = 2 ∨ P");
        fail("∀ P: U, 2 = 2 ∧ P");
        success("∀ P: U, forall x: ℤ, 2 * x < 6 ∧ P -> 2 * x < 5");
        fail("∀ P: U, forall x: ℤ, 2 * x < 6 ∨ P -> 2 * x < 5");
        success("∀ P: U, forall x: ℤ, 2 * x < 6 -> 2 * x < 5 ∨ P");
        fail("∀ P: U, forall x: ℤ, 2 * x < 6 -> 2 * x < 5 ∧ P");
    }

    #[test]
    fn fail_simple() {
        fail("forall x: ℤ, 2 < x");
    }

    #[test]
    fn fail_tight() {
        fail("forall x: ℤ, 5 < 2 * x -> 6 < 2 * x");
    }

    #[test]
    fn success_lia_hyp() {
        run_interactive_to_end("forall x: ℤ, x + 2 < x + 1 -> False", "intros\nlia");
    }

    #[test]
    fn calculator_mode() {
        with_params("lia=calculator", || {
            success("1 < 2");
            success("2 + 2 = 4");
            fail("1 < 1");
            fail("2 < 1");
            success("-1000000000000000000 < 1");
            fail("∀ x: ℤ, 2 * x = 4 -> x = 2");
        });
        success("∀ x: ℤ, 2 * x = 4 -> x = 2");
    }
}
