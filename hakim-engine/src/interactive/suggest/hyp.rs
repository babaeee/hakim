use crate::{
    brain::{remove_unused_var, Abstraction, Term},
    interactive::Frame,
};

use super::{SuggClass::*, SuggRule, Suggestion};

const HYP_RULES: &[SuggRule] = &[
    SuggRule {
        class: Destruct,
        tactic: &["destruct $n with (ex_ind ? ?) to ($n_value $n_proof)"],
        is_default: true,
    },
    SuggRule {
        class: Rewrite,
        tactic: &["rewrite $n"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a = b", "b = a"),
        tactic: &["apply eq_sym in $n"],
        is_default: false,
    },
    SuggRule {
        class: Pattern("a ⊆ b", "∀ x: T, x ∈ a -> x ∈ b"),
        tactic: &["apply included_unfold in $n"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b}", "a = b"),
        tactic: &["apply singleton_unfold in $n"],
        is_default: true,
    },
    SuggRule {
        class: Pattern("a ∈ {b | f b}", "f a"),
        tactic: &["apply set_from_func_unfold in $n"],
        is_default: true,
    },
    SuggRule {
        class: Contradiction,
        tactic: &["apply empty_intro in $n", "apply (False_ind $n ?)"],
        is_default: true,
    },
    SuggRule {
        class: Contradiction,
        tactic: &["apply (False_ind $n ?)"],
        is_default: true,
    },
    SuggRule {
        class: Destruct,
        tactic: &["destruct $n with (or_ind ? ?)"],
        is_default: true,
    },
    SuggRule {
        class: Destruct,
        tactic: &["destruct $n with (and_ind ? ?) to ($n_l $n_r)"],
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
    let hyp = frame.hyps.get(name).unwrap().ty.clone();
    match hyp.as_ref() {
        Term::Forall(Abstraction { body, .. }) => {
            if remove_unused_var(body.clone(), 0).is_some() {
            } else {
                let new_name = frame.engine.generate_name(&format!("{name}_ex"));
                r.push(Suggestion::newq1default(
                    Instantiate,
                    &format!("add_hyp {new_name} := ({name} ($0))"),
                    &format!("$enter_value_that_you_want_to_put_on_foreign<${body:?}$>"),
                ));
            }
        }
        Term::App { func, op: _ } => {
            if let Term::App { func, op: _ } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name.as_str() == "ex" && frame.engine.has_library("Logic") {
                        r.push(Suggestion::newq1default(
                            DestructWithName,
                            &format!("destruct {name} with (ex_ind ? ?) to ($0 $0_property)"),
                            "$enter_a_name:",
                        ))
                    };
                }
            }
        }
        _ => (),
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
