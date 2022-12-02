/*
 تاکتیک برای پیدا کردن عین هدف در بین فرض ها یا وجود یک فرض و مخالفش در بین فرض ها
*/
use super::Result;
use crate::{
    analysis::logic::{LogicArena, LogicBuilder, LogicValue},
    brain::TermRef,
    interactive::Frame,
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
    LogicValue::from(PropStatement::Atom(term))
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
