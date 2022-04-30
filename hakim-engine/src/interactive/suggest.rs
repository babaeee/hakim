use std::fmt::Display;

use crate::Term;

#[cfg(test)]
mod tests;

mod hyp;
pub use hyp::{suggest_on_hyp, suggest_on_hyp_dblclk};

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum SuggClass {
    Intros,
    IntrosWithName,
    Destruct,
    Rewrite,
    Contradiction,
    Pattern(&'static str, &'static str),
}

impl Display for SuggClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Intros => write!(f, "$intros"),
            IntrosWithName => write!(f, "$intros_with_name"),
            Destruct => write!(f, "$destruct"),
            Rewrite => write!(f, "$rewrite"),
            Contradiction => write!(f, "$contradiction"),
            Pattern(a, b) => write!(f, "{a} ⇒ {b}"),
        }
    }
}

use SuggClass::*;

use super::Frame;

#[derive(Debug, Clone, Copy)]
pub struct SuggRule {
    pub class: SuggClass,
    pub tactic: &'static [&'static str],
    pub questions: &'static [&'static str],
    pub is_default: bool,
}

impl From<SuggRule> for Suggestion {
    fn from(sugg: SuggRule) -> Self {
        Self {
            class: sugg.class,
            tactic: sugg.tactic.iter().map(|x| x.to_string()).collect(),
            questions: sugg.questions.iter().map(|x| x.to_string()).collect(),
            is_default: sugg.is_default,
        }
    }
}

impl SuggRule {
    fn try_on_goal(self, frame: Frame) -> Option<Suggestion> {
        frame.run_tactic(self.tactic[0]).ok()?;
        Some(self.into())
    }

    fn try_on_hyp(self, name: &str, frame: Frame) -> Option<Suggestion> {
        frame.run_tactic(&self.tactic[0].replace("$n", name)).ok()?;
        let mut r: Suggestion = self.into();
        r.tactic = r
            .tactic
            .into_iter()
            .map(|x| x.replace("$n", name))
            .collect();
        Some(r)
    }
}

#[derive(Debug)]
pub struct Suggestion {
    pub class: SuggClass,
    pub tactic: Vec<String>,
    pub questions: Vec<String>,
    pub is_default: bool,
}

impl Suggestion {
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

const GOAL_RULES: &[SuggRule] = &[
    SuggRule {
        class: Destruct,
        tactic: &["apply and_intro"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("A ∨ B", "~ B ⊢ A"),
        tactic: &["apply or_to_imply", "intros"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("A ∨ B", "~ A ⊢ B"),
        tactic: &["apply or_sym", "apply or_to_imply", "intros"],
        questions: &[],
        is_default: false,
    },
    SuggRule {
        class: Pattern("A = B", "A ⊆ B ∧ B ⊆ A"),
        tactic: &["apply set_equality"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ x ∪ y", "a ∈ x ∨ a ∈ y"),
        tactic: &["apply union_fold"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b}", "a = b"),
        tactic: &["apply singleton_fold"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b | f b}", "f a"),
        tactic: &["apply set_from_func_fold"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ⊆ b", "∀ x: T, x ∈ a -> x ∈ b"),
        tactic: &["apply included_fold"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("A ∨ B", "A"),
        tactic: &["apply or_introl"],
        questions: &[],
        is_default: false,
    },
    SuggRule {
        class: Pattern("A ∨ B", "B"),
        tactic: &["apply or_intror"],
        questions: &[],
        is_default: false,
    },
    SuggRule {
        class: Pattern("A ∧ B", "A, B"),
        tactic: &["apply and_intro"],
        questions: &[],
        is_default: true,
    },
];

pub fn suggest_on_goal(goal: &Term, frame: &Frame) -> Vec<Suggestion> {
    let mut r = vec![];
    for rule in GOAL_RULES {
        if let Some(x) = rule.try_on_goal(frame.clone()) {
            r.push(x);
        }
    }
    match goal {
        Term::Forall(_) => {
            r.push(Suggestion::new_default(Intros, "intros"));
            r.push(Suggestion {
                class: IntrosWithName,
                tactic: vec!["intros $0".to_string()],
                questions: vec!["$enter_a_name:".to_string()],
                is_default: false,
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
    for sugg in suggs {
        if sugg.is_default {
            return Some(sugg);
        }
    }
    None
}
