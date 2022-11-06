use crate::brain::Term;
use crate::interactive::Frame;

use super::Applicablity;
use super::SuggClass::*;
use super::Suggestion;

pub fn suggest_on_goal(goal: &Term, frame: &Frame) -> Vec<Suggestion> {
    let mut r = vec![];
    for rule in &frame.engine.goal_suggs {
        if let Some(x) = rule.try_on_goal(frame.clone()) {
            r.push(x);
        }
    }
    match goal {
        Term::Forall(_) => {
            r.push(Suggestion::new_default(Intros, "intros"));
            r.push(Suggestion {
                class: IntrosWithName,
                tactic: "intros $0".to_string(),
                questions: vec!["$enter_a_name:".to_string()],
                applicablity: Applicablity::Normal,
            });
        }
        Term::App { func, op: _ } => {
            if let Term::App { func, op: _ } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name.as_str() == "ex" {
                        r.push(Suggestion::newq1default(
                            Destruct,
                            "apply (ex_intro ? ? ($0))",
                            "$enter_value_that_satisfy:",
                        ))
                    };
                }
            }
        }
        _ => {}
    }
    r
}

pub fn suggest_on_goal_dblclk(goal: &Term, frame: &Frame) -> Option<Suggestion> {
    let suggs = suggest_on_goal(goal, frame);
    suggs.into_iter().find(|sugg| sugg.is_default())
}
