use crate::{
    brain::{subst, Term},
    interactive::Frame,
    term_ref, Abstraction,
};

use super::{Error::*, Result};

pub fn intros_one(frame: &mut Frame, name: &str) -> Result<()> {
    let goal = frame.goal.clone();
    match goal.as_ref() {
        Term::Forall(Abstraction { var_ty, body }) => {
            frame.add_hyp_with_name(name, var_ty.clone())?;
            frame.goal = subst(body.clone(), term_ref!(axiom name, var_ty));
            Ok(())
        }
        _ => Err(BadGoal("intros expects forall")),
    }
}

pub fn intros(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let mut args = args.peekable();
    if args.peek().is_none() {
        while let Term::Forall(Abstraction { var_ty, body }) = frame.goal.clone().as_ref() {
            let name = frame.engine.generate_name("H");
            frame.add_hyp_with_name(&name, var_ty.clone())?;
            frame.goal = subst(body.clone(), term_ref!(axiom name, var_ty));
        }
    } else {
        for name in args {
            intros_one(&mut frame, &name)?;
        }
    }
    Ok(vec![frame])
}
