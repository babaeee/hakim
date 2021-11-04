use crate::{engine::Engine, TermRef};

use super::{detect_class, SuggClass::*, Suggestion, TermClass};

pub fn suggest_on_hyp_menu(engine: &Engine, name: &str, ty: &TermRef) -> Vec<Suggestion> {
    let c = detect_class(ty);
    let mut r = vec![];
    match c {
        TermClass::Eq => {
            r.push(Suggestion::new(Rewrite, &format!("rewrite {}", name)));
            r.push(Suggestion::new(
                Swap,
                &format!("apply (eq_sym ? ? ?) in {}", name),
            ));
        }
        TermClass::Exists => {
            let val_name = engine.generate_name(&format!("{}_value", name));
            let proof_name = engine.generate_name(&format!("{}_proof", name));
            r.push(Suggestion {
                class: Destruct,
                tactic: vec![
                    format!("apply ex_ind (3:={})", name),
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
                    format!("apply ex_ind (3:={})", name),
                    format!("remove_hyp {}", name),
                    format!("intros {} {}", val_name, proof_name),
                ],
                questions: vec![],
            }
        }
        TermClass::Forall | TermClass::Unknown => return None,
    })
}
