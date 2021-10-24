use crate::{
    brain::{subst, Term},
    engine::interactive::{InteractiveFrame, InteractiveSnapshot},
    term_ref,
};

use super::{Error::*, Result};

pub fn intros_one(frame: &mut InteractiveFrame, name: &str) -> Result<()> {
    let goal = frame.goal.clone();
    match goal.as_ref() {
        Term::Forall { var_ty, body } => {
            frame.add_hyp_with_name(&name, var_ty.clone())?;
            frame.goal = subst(body.clone(), term_ref!(axiom name, var_ty));
            Ok(())
        }
        _ => Err(BadGoal("intros expects forall")),
    }
}

pub fn intros(
    snapshot: &InteractiveSnapshot,
    args: impl Iterator<Item = String>,
) -> Result<InteractiveSnapshot> {
    let mut snapshot = snapshot.clone();
    let mut frame = snapshot.pop_frame();
    let mut args = args.peekable();
    if args.peek().is_none() {
        loop {
            match frame.goal.clone().as_ref() {
                Term::Forall { var_ty, body } => {
                    let name = frame.engine.generate_name("x");
                    frame.add_hyp_with_name(&name, var_ty.clone())?;
                    frame.goal = subst(body.clone(), term_ref!(axiom name, var_ty));
                }
                _ => break,
            }
        }
    } else {
        for name in args {
            intros_one(&mut frame, &name)?;
        }
    }
    snapshot.push_frame(frame);
    Ok(snapshot)
}
