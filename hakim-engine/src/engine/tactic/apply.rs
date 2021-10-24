use crate::{
    app_ref,
    brain::{
        contains_wild,
        infer::{match_and_infer, type_of_and_infer, InferResults},
        type_of,
    },
    engine::interactive::InteractiveSnapshot,
    term_ref, Term, TermRef,
};

use super::{get_one_arg, Error::*, Result};

pub fn get_forall_depth(term: &TermRef) -> usize {
    match term.as_ref() {
        Term::Forall { body, .. } => get_forall_depth(body) + 1,
        _ => 0,
    }
}

pub fn apply(
    snapshot: &InteractiveSnapshot,
    args: impl Iterator<Item = String>,
) -> Result<InteractiveSnapshot> {
    let exp = &get_one_arg(args, "apply")?;
    let mut snapshot = snapshot.clone();
    let frame = snapshot.pop_frame();
    let term = frame.engine.parse_text(exp)?;
    let ty = type_of(term.clone())?;
    let d_forall = get_forall_depth(&ty);
    let mut twa = term;
    for i in 0..d_forall {
        twa = app_ref!(twa, term_ref!(_ i));
    }
    let mut infers = InferResults::new(d_forall);
    let twa_ty = type_of_and_infer(twa, &mut infers)?;
    match_and_infer(twa_ty, frame.goal.clone(), &mut infers)?;
    for i in 0..d_forall {
        let mut frame = frame.clone();
        if !contains_wild(&infers.terms[i]) {
            continue;
        }
        if !contains_wild(&infers.tys[i]) {
            frame.goal = infers.tys[i].clone();
            snapshot.push_frame(frame);
        } else {
            return Err(CanNotFindInstance(i, ty));
        }
    }
    Ok(snapshot)
}
