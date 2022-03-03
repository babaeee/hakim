use crate::interactive::Frame;

use super::{SuggClass::*, SuggRule, Suggestion};

const HYP_RULES: &[SuggRule] = &[
    SuggRule {
        class: Destruct,
        tactic: &[
            "apply (ex_ind ? ? $n)",
            "remove_hyp $n",
            "intros $n_value $n_proof",
        ],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Rewrite,
        tactic: &["rewrite $n"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a = b", "b = a"),
        tactic: &["apply eq_sym in $n"],
        questions: &[],
        is_default: false,
    },
    SuggRule {
        class: Pattern("a ⊆ b", "∀ x: T, x ∈ a -> x ∈ b"),
        tactic: &["apply included_unfold in $n"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b}", "a = b"),
        tactic: &["apply singleton_unfold in $n"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b | f b}", "f a"),
        tactic: &["apply set_from_func_unfold in $n"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Contradiction,
        tactic: &["apply empty_intro in $n", "apply (False_ind $n ?)"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Contradiction,
        tactic: &["apply (False_ind $n ?)"],
        questions: &[],
        is_default: true,
    },
    SuggRule {
        class: Destruct,
        tactic: &["chain (apply (or_ind ? ? $n)) (remove_hyp $n) (intros $n)"],
        questions: &[],
        is_default: true,
    },
];

pub fn suggest_on_hyp(frame: &Frame, name: &str) -> Vec<Suggestion> {
    let mut r = vec![];
    for rule in HYP_RULES {
        if let Some(x) = rule.try_on_hyp(name, frame.clone()) {
            r.push(x);
        }
    }
    r
}

pub fn suggest_on_hyp_dblclk(frame: &Frame, name: &str) -> Option<Suggestion> {
    let suggs = suggest_on_hyp(frame, name);
    for sugg in suggs {
        if sugg.is_default {
            return Some(sugg);
        }
    }
    None
}
