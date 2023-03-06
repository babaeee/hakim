/*
 تاکتیک برای پیدا کردن عین هدف در بین فرض ها یا وجود یک فرض و مخالفش در بین فرض ها
*/
use super::Result;
use crate::{
    analysis::{
        arith::ConstRepr,
        big_fraction::BigFraction,
        logic::{LogicArena, LogicBuilder, LogicValue},
    },
    app_ref,
    brain::{
        detect::{detect_q_set, detect_z_ty},
        Term, TermRef,
    },
    interactive::Frame,
    library::prelude::{inset, q_set},
};
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PropStatement {
    Atom(TermRef),
    Not(TermRef),
}
use PropStatement::*;

use std::collections::HashMap;
fn convert(
    term: TermRef,
    _logic_arena: LogicArena<'_, PropStatement>,
) -> LogicValue<'_, PropStatement> {
    if let Term::App { func, op: set } = term.as_ref() {
        if let Term::App { func, op } = func.as_ref() {
            if let Term::App { func: _, op: _ } = func.as_ref() {
                if detect_q_set(set) {
                    if BigFraction::from_term(op).is_some() {
                        return LogicValue::True;
                    }
                    if let Term::App { func, op: op2 } = op.as_ref() {
                        if let Term::App { func, op: op1 } = func.as_ref() {
                            if let Term::App { func, op: ty } = func.as_ref() {
                                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                                    match unique_name.as_str() {
                                        "plus" | "minus" | "mult" => {
                                            return convert(in_q_term(op1.clone()), _logic_arena)
                                                .and(
                                                    convert(in_q_term(op2.clone()), _logic_arena),
                                                    _logic_arena,
                                                );
                                        }
                                        "div" => {
                                            if detect_z_ty(ty) {
                                                return LogicValue::True;
                                            }
                                            return convert(in_q_term(op1.clone()), _logic_arena)
                                                .and(
                                                    convert(in_q_term(op2.clone()), _logic_arena),
                                                    _logic_arena,
                                                );
                                        }
                                        _ => (),
                                    }
                                }
                            }
                            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                                if unique_name == "neg" {
                                    return convert(in_q_term(op2.clone()), _logic_arena);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = ty.as_ref() {
                    if unique_name == "extR" {
                        if let Term::Axiom { unique_name, .. } = func.as_ref() {
                            if unique_name == "eq" {
                                let Some(t1) = ext_r_type(op1.clone()) else {
                                    return LogicValue::unknown();
                                };
                                let Some(t2) = ext_r_type(op2.clone()) else {
                                    return  LogicValue::unknown();
                                };
                                if t1 != t2 {
                                    return LogicValue::False;
                                } else if t1 == t2 && t1 != 0 {
                                    return LogicValue::True;
                                } else {
                                    return LogicValue::unknown();
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    LogicValue::from(PropStatement::Atom(term))
}
fn in_q_term(num: TermRef) -> TermRef {
    app_ref!(inset(), crate::library::prelude::r(), num, q_set())
}
fn ext_r_type(r: TermRef) -> Option<i32> {
    return match r.as_ref() {
        Term::Axiom { unique_name, .. } => {
            if unique_name == "p_infty" {
                Some(1)
            } else if unique_name == "m_infty" {
                Some(-1)
            } else {
                None
            }
        }
        Term::App { func, op: _ } => {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "Fin" {
                    Some(0)
                } else {
                    None
                }
            } else {
                None
            }
        }
        _ => None,
    };
}
fn check_contradiction(a: &[PropStatement]) -> bool {
    let mut map = HashMap::<TermRef, bool>::new();
    for x in a.iter() {
        match x {
            Atom(t) => {
                if let Some(x) = map.get(t) {
                    if !*x {
                        return true;
                    }
                } else {
                    map.insert(t.clone(), true);
                }
            }
            Not(t) => {
                if let Some(x) = map.get(t) {
                    if *x {
                        return true;
                    }
                } else {
                    map.insert(t.clone(), false);
                }
            }
        }
    }
    false
}
fn negator(x: PropStatement) -> PropStatement {
    match x {
        Atom(t) => Not(t),
        Not(t) => Atom(t),
    }
}
pub fn assumption(frame: Frame) -> Result<Vec<Frame>> {
    LogicBuilder::build_tactic("assumption", frame, convert, check_contradiction, negator)
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nassumption");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "assumption");
    }

    #[test]
    fn impl_todo() {
        success("∀ P Q R S: U, R -> R");
        success("∀ P Q R S: U, (R -> S) -> R -> (S -> False) ∨ Q -> Q");
    }
    #[test]
    fn chars() {
        success("~ 'r' = 'u'");
    }
    #[test]
    fn rational_numbers_checks() {
        success("2. ∈ ℚ ");
        success("∀ x y z t, x ∈ ℚ -> y ∈ ℚ -> z ∈ ℚ -> t ∈ ℚ -> x * y + z - t ∈ ℚ ");
        success("∀ n, 1. - n / 1 * 1. ∈ ℚ");
    }
    #[test]
    fn eq_ext_r_tests() {
        success("~ p_infty = m_infty");
        success("~ p_infty = Fin 1.");
        success("~ Fin 2. = m_infty");
        success("m_infty = m_infty");
        fail("Fin 1. = Fin 2.");
    }
}
