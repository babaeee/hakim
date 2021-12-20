use crate::{engine::Engine, TermRef};

use super::{detect_class, SetTermClass, SuggClass::*, Suggestion, TermClass};

pub fn suggest_on_hyp_menu(engine: &Engine, name: &str, ty: &TermRef) -> Vec<Suggestion> {
    let c = detect_class(ty);
    let mut r = vec![];
    match c {
        TermClass::Eq => {
            r.push(Suggestion::new(Rewrite, &format!("rewrite {}", name)));
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
                        r.push(Suggestion::new(
                            Pattern("a ∈ {b}", "a = b"),
                            &format!("apply (singleton_unfold ? ? ?) in {}", name),
                        ));
                    }
                    SetTermClass::Unknown => {}
                }
            }
        }
        TermClass::SetIncluded(..) => {
            if engine.has_library("Set") {
                r.push(Suggestion::new(
                    Pattern("a ⊆ b", "∀ x: T, x ∈ a -> x ∈ b"),
                    &format!("apply (included_unfold ? ? ?) in {}", name),
                ));
            }
        }
        TermClass::Exists => {
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
            });
        }
        TermClass::Forall | TermClass::Unknown => (),
    }
    r
}

pub fn suggest_on_hyp_dblclk(engine: &Engine, name: &str, ty: &TermRef) -> Option<Suggestion> {
    let c = detect_class(ty);
    Some(match c {
        TermClass::Eq => Suggestion::new(Rewrite, &format!("rewrite {}", name)),
        TermClass::Exists => {
            let val_name = engine.generate_name(&format!("{}_value", name));
            let proof_name = engine.generate_name(&format!("{}_proof", name));
            Suggestion {
                class: Destruct,
                tactic: vec![
                    format!("apply (ex_ind ? ? {})", name),
                    format!("remove_hyp {}", name),
                    format!("intros {} {}", val_name, proof_name),
                ],
                questions: vec![],
            }
        }
        _ => return None,
    })
}
