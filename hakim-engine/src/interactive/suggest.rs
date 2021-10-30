use crate::{engine::Engine, Term, TermRef};

#[derive(PartialEq, Eq, Debug)]
pub enum SuggClass {
    Intros,
    IntrosWithName,
    Destruct,
    Rewrite,
}

use SuggClass::*;

#[derive(Debug)]
pub struct Suggestion {
    pub class: SuggClass,
    pub tactic: Vec<String>,
    pub questions: Vec<String>,
}

impl Suggestion {
    fn new(class: SuggClass, t: &str) -> Self {
        Self {
            class,
            tactic: vec![t.to_string()],
            questions: vec![],
        }
    }

    fn newq1(class: SuggClass, t: &str, q: &str) -> Self {
        Self {
            class,
            tactic: vec![t.to_string()],
            questions: vec![q.to_string()],
        }
    }
}

enum TermClass {
    Forall,
    Exists,
    Eq,
    Unknown,
}

fn detect_class(t: &TermRef) -> TermClass {
    match t.as_ref() {
        Term::Forall(_) => return TermClass::Forall,
        Term::App { func, op: _ } => {
            if let Term::App { func, op: _ } = func.as_ref() {
                if let Term::App { func, op: _ } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        return match unique_name.as_str() {
                            "eq" => TermClass::Eq,
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

pub fn suggest_on_goal_dblclk(goal: &TermRef) -> Option<Suggestion> {
    let c = detect_class(goal);
    return Some(match c {
        TermClass::Forall => Suggestion::new(Intros, "intros"),
        TermClass::Exists => Suggestion::newq1(Destruct, "apply ex_intro (3:=$0)", "Enter value"),
        TermClass::Eq | TermClass::Unknown => return None,
    });
}

pub fn suggest_on_hyp_dblclk(engine: &Engine, name: &str, ty: &TermRef) -> Option<Suggestion> {
    let c = detect_class(ty);
    return Some(match c {
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
    });
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive;

    use super::SuggClass;

    fn check_goal_dblclk(goal: &str, tactics: &str, class: SuggClass, ans: Vec<&str>) {
        let mut session = run_interactive(goal, tactics);
        let sugg = session.suggest_on_goal_dblclk().unwrap();
        if sugg.class != class {
            panic!("bad sugg class: expected {:?}\nSugg:{:?}", class, sugg);
        }
        let e = session.run_suggestion(sugg, ans.into_iter().map(|x| x.to_owned()).collect());
        match e {
            Ok(_) => (),
            Err(e) => {
                panic!(
                    "failed to run sugg. Error: {:?}\nMonitor:\n{}",
                    e,
                    session.monitor_string()
                );
            }
        }
    }

    #[test]
    fn exist_goal() {
        check_goal_dblclk(
            "∀ P: ℤ -> U, (∀ x: ℤ, P x -> P (2*x)) -> (∃ b: ℤ, P b) -> ∃ b: ℤ, P (2*b)",
            r#"
            intros P px_p2x exP
            apply ex_ind (3:=exP)
            intros exP_value exP_proof
            "#,
            SuggClass::Destruct,
            vec!["exP_value"],
        );
    }
}
