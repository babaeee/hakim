use crate::{Term, TermRef};

#[cfg(test)]
mod tests;

mod hyp;
pub use hyp::{suggest_on_hyp, suggest_on_hyp_dblclk};

#[derive(PartialEq, Eq, Debug)]
pub enum SuggClass {
    Intros,
    IntrosWithName,
    Destruct,
    Rewrite,
    Contradiction,
    Pattern(&'static str, &'static str),
}

use SuggClass::*;

#[derive(Debug)]
pub struct Suggestion {
    pub class: SuggClass,
    pub tactic: Vec<String>,
    pub questions: Vec<String>,
    pub is_default: bool,
}

impl Suggestion {
    fn new(class: SuggClass, t: &str) -> Self {
        Self {
            class,
            tactic: vec![t.to_string()],
            questions: vec![],
            is_default: false,
        }
    }

    fn new_default(class: SuggClass, t: &str) -> Self {
        Self {
            class,
            tactic: vec![t.to_string()],
            questions: vec![],
            is_default: true,
        }
    }

    fn newq1default(class: SuggClass, t: &str, q: &str) -> Self {
        Self {
            class,
            tactic: vec![t.to_string()],
            questions: vec![q.to_string()],
            is_default: true,
        }
    }
}

enum SetTermClass {
    Empty,
    Singleton,
    Unknown,
}

enum TermClass {
    Forall,
    Exists,
    False,
    Eq,
    SetMember(SetTermClass),
    SetIncluded(SetTermClass, SetTermClass),
    Unknown,
}

fn detect_set_class(t: &Term) -> SetTermClass {
    match dbg!(t) {
        Term::App { func, op: _ } => match func.as_ref() {
            Term::App { func, op: _ } => match func.as_ref() {
                Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                    "set_singleton" => SetTermClass::Singleton,
                    _ => SetTermClass::Unknown,
                },
                _ => SetTermClass::Unknown,
            },
            Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                "set_empty" => SetTermClass::Empty,
                _ => SetTermClass::Unknown,
            },
            _ => SetTermClass::Unknown,
        },
        _ => SetTermClass::Unknown,
    }
}

fn detect_class(t: &Term) -> TermClass {
    match t {
        Term::Forall(_) => return TermClass::Forall,
        Term::Axiom { unique_name, .. } => {
            return match unique_name.as_str() {
                "False" => TermClass::False,
                _ => TermClass::Unknown,
            }
        }
        Term::App { func, op: op1 } => {
            if let Term::App { func, op: op2 } = func.as_ref() {
                if let Term::App { func, op: _ } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        return match unique_name.as_str() {
                            "eq" => TermClass::Eq,
                            "inset" => TermClass::SetMember(detect_set_class(op1)),
                            "included" => {
                                TermClass::SetIncluded(detect_set_class(op1), detect_set_class(op2))
                            }
                            _ => TermClass::Unknown,
                        };
                    }
                }
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    return match unique_name.as_str() {
                        "ex" => TermClass::Exists,
                        _ => TermClass::Unknown,
                    };
                }
            }
        }
        _ => (),
    }
    TermClass::Unknown
}

pub fn suggest_on_goal(goal: &Term) -> Vec<Suggestion> {
    let c = detect_class(goal);
    let mut r = vec![];
    match c {
        TermClass::Forall => {
            r.push(Suggestion::new_default(Intros, "intros"));
            r.push(Suggestion {
                class: IntrosWithName,
                tactic: vec!["intros $0".to_string()],
                questions: vec!["$enter_a_name:".to_string()],
                is_default: false,
            });
        }
        TermClass::Exists => r.push(Suggestion::newq1default(
            Destruct,
            "apply (ex_intro ? ? ($0))",
            "$enter_value_that_satisfy:",
        )),
        TermClass::SetIncluded(_, _) => {
            r.push(Suggestion::new_default(
                Pattern("a ⊆ b", "∀ x: T, x ∈ a -> x ∈ b"),
                "apply included_fold",
            ));
        }
        _ => {}
    }
    r
}

pub fn suggest_on_goal_dblclk(goal: &TermRef) -> Option<Suggestion> {
    let suggs = suggest_on_goal(goal);
    for sugg in suggs {
        if sugg.is_default {
            return Some(sugg);
        }
    }
    None
}
