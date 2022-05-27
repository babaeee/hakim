use crate::{
    brain::{remove_unused_var, Abstraction, Term},
    interactive::Frame,
};

use super::{SuggClass::*, Suggestion};

pub fn suggest_on_hyp(frame: &Frame, name: &str) -> Vec<Suggestion> {
    let mut r = vec![];
    for rule in dbg!(&frame.engine.hyp_suggs) {
        if let Some(x) = rule.try_on_hyp(name, frame.clone()) {
            r.push(x);
        }
    }
    let hyp = frame.get_hyp_by_name(name).unwrap().ty.clone();
    match hyp.as_ref() {
        Term::Forall(Abstraction { body, var_ty, .. }) => {
            if remove_unused_var(body.clone(), 0).is_some() {
                let next_h = frame.engine.generate_name("H");
                let new_name = frame.engine.generate_name(&format!("{name}_o"));
                let ty_str = frame.engine.pretty_print(var_ty);
                r.push(Suggestion {
                    class: Instantiate,
                    tactic: vec![
                        format!("add_hyp ({ty_str})"),
                        format!("remove_hyp {name}"),
                        format!("Switch 1"),
                        format!("add_hyp {new_name} := ({name} {next_h})"),
                        format!("remove_hyp {next_h}"),
                        format!("remove_hyp {name}"),
                    ],
                    questions: vec![],
                    is_default: true,
                });
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
                    if unique_name.as_str() == "ex" && frame.engine.has_library("/Logic") {
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
