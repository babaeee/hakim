use crate::brain::Term;
use crate::interactive::Frame;

use super::SuggClass::*;
use super::SuggRule;
use super::Suggestion;

const GOAL_RULES: &[SuggRule] = &[
    SuggRule {
        class: Destruct,
        tactic: &["apply and_intro"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("A ∨ B", "~ B ⊢ A"),
        tactic: &["apply or_to_imply", "intros"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("A ∨ B", "~ A ⊢ B"),
        tactic: &["apply or_sym", "apply or_to_imply", "intros"],
        is_default: false,
    },
    SuggRule {
        class: Pattern("A = B", "A ⊆ B ∧ B ⊆ A"),
        tactic: &["apply set_equality"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ x ∪ y", "a ∈ x ∨ a ∈ y"),
        tactic: &["apply union_fold"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b}", "a = b"),
        tactic: &["apply singleton_fold"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b | f b}", "f a"),
        tactic: &["apply set_from_func_fold"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ⊆ b", "∀ x: T, x ∈ a -> x ∈ b"),
        tactic: &["apply included_fold"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("A ∨ B", "A"),
        tactic: &["apply or_introl"],
        is_default: false,
    },
    SuggRule {
        class: Pattern("A ∨ B", "B"),
        tactic: &["apply or_intror"],
        is_default: false,
    },
    SuggRule {
        class: Pattern("A ∧ B", "A, B"),
        tactic: &["apply and_intro"],
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
