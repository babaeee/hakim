use super::{Error::*, Result};
use crate::{
    analysis::{
        arith::{LinearPoly, Poly},
        logic::{LogicArena, LogicBuilder, LogicTree},
    },
    brain::{Term, TermRef},
    interactive::Frame,
};

fn convert(term: TermRef, arena: LogicArena<'_, Poly>) -> &LogicTree<'_, Poly> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "lt" {
                    let d = Poly::from_subtract(op2.clone(), op1.clone());
                    return arena.alloc(LogicTree::Atom(d));
                }
            }
        }
    }
    arena.alloc(LogicTree::Unknown)
}

fn check_contradiction(polies: &[Poly]) -> bool {
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
                            if ub <= *prev_ub {
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
    let logic_builder = LogicBuilder::new(convert);
    logic_builder.and_not_term(frame.goal);
    for (_, hyp) in frame.hyps {
        logic_builder.and_term(hyp);
    }
    if logic_builder.check_contradiction(check_contradiction, negator) {
        Ok(vec![])
    } else {
        Err(CanNotSolve("lia"))
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

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
    }

    #[test]
    fn success_lia_use_integer() {
        success("forall x: ℤ, 4 < 2 * x -> 5 < 2 * x");
        success("forall x: ℤ, 2 * x < 6 -> 2 * x < 5");
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
}
