use crate::{brain::Term, engine::Engine};

use super::{detect_class, SetTermClass, SuggClass::*, Suggestion, TermClass};

pub fn suggest_on_hyp(engine: &Engine, name: &str, ty: &Term) -> Vec<Suggestion> {
    let c = detect_class(ty);
    let mut r = vec![];
    match c {
        TermClass::Eq => {
            r.push(Suggestion::new_default(
                Rewrite,
                &format!("rewrite {}", name),
            ));
            if engine.has_library("Eq") {
                r.push(Suggestion::new(
                    Pattern("a = b", "b = a"),
                    &format!("apply (eq_sym ? ? ?) in {}", name),
                ));
            }
        }
        TermClass::SetMember(x) => {
            if engine.has_library("Set") {
                match x {
                    SetTermClass::Singleton => {
                        r.push(Suggestion::new_default(
                            Pattern("a ∈ {b}", "a = b"),
                            &format!("apply (singleton_unfold ? ? ?) in {}", name),
                        ));
                    }
                    SetTermClass::Empty => r.push(Suggestion {
                        class: Contradiction,
                        tactic: vec![
                            format!("apply (empty_intro ? ?) in {}", name),
                            format!("apply (False_ind {} ?)", name),
                        ],
                        questions: vec![],
                        is_default: true,
                    }),
                    SetTermClass::Unknown => {}
                }
            }
        }
        TermClass::SetIncluded(..) => {
            if engine.has_library("Set") {
                r.push(Suggestion::new_default(
                    Pattern("a ⊆ b", "∀ x: T, x ∈ a -> x ∈ b"),
                    &format!("apply (included_unfold ? ? ?) in {}", name),
                ));
            }
        }
        TermClass::False => {
            if engine.has_library("Logic") {
                r.push(Suggestion::new_default(
                    Contradiction,
                    &format!("apply (False_ind {} ?)", name),
                ));
            }
        }
        TermClass::Exists => {
            if engine.has_library("Logic") {
                let val_name = engine.generate_name(&format!("{}_value", name));
                let proof_name = engine.generate_name(&format!("{}_proof", name));
                r.push(Suggestion {
                    class: Destruct,
                    tactic: vec![
                        format!("apply (ex_ind ? ? {})", name),
                        format!("remove_hyp {}", name),
                        format!("intros {} {}", val_name, proof_name),
                    ],
                    questions: vec![],
                    is_default: true,
                });
            }
        }
        TermClass::Forall | TermClass::Unknown => (),
    }
    r
}

pub fn suggest_on_hyp_dblclk(engine: &Engine, name: &str, ty: &Term) -> Option<Suggestion> {
    let suggs = suggest_on_hyp(engine, name, ty);
    for sugg in suggs {
        if sugg.is_default {
            return Some(sugg);
        }
    }
    None
}
