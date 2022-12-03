/*
 تاکتیک برای پیدا کردن عین هدف در بین فرض ها یا وجود یک فرض و مخالفش در بین فرض ها
*/
use super::Result;
use crate::{
    analysis::logic::{LogicArena, LogicBuilder, LogicValue},
    app_ref,
    brain::{Term, TermRef},
    interactive::Frame,
    library::prelude::is_q,
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
    /*  if let Term::App { func, op } = term.as_ref() {
        if let Term::Axiom {unique_name, .. } = func.as_ref() {
            if unique_name == "is_q" {
                if let Term::App { func, op: op2 } = op.as_ref() {
                    if let Term::App { func, op: op1 } = func.as_ref() {
                        if let Term::App { func, op } = func.as_ref() {
                            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                                match unique_name.as_str() {
                                    "plus" | "minus" => convert(is_q_term(op1), logic_arena).and(convert(is_q_term(op2), logic_arena), arena);

                                "mult" if detect_z_ty(op) || detect_r_ty(op) => Mult(
                                    term_ref_to_arith(op1.clone(), arena),
                                    term_ref_to_arith(op2.clone(), arena),
                                ),
                                "div" if detect_z_ty(op) || detect_r_ty(op) => Div(
                                    term_ref_to_arith(op1.clone(), arena),
                                    term_ref_to_arith(op2.clone(), arena),
                                ),
                                _ => atom_normalizer(t),
                            },
                            _ => atom_normalizer(t),
                        },

            }
        }
    }*/
    LogicValue::from(PropStatement::Atom(term))
}
fn is_q_term(r: TermRef) -> TermRef {
    app_ref!(is_q(), r)
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
    use crate::interactive::tests::run_interactive_to_end; //run_interactive_to_fail};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nassumption");
    }

    /*    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "assumption");
    }*/

    #[test]
    fn impl_todo() {
        success("∀ P Q R S: U, R -> R");
        success("∀ P Q R S: U, (R -> S) -> R -> (S -> False) ∨ Q -> Q");
    }
    #[test]
    fn chars() {
        success("~ 'r' = 'u'");
    }
}
