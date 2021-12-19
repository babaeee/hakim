use crate::{
    brain::{subst, Term},
    interactive::Frame,
    term_ref, Abstraction,
};

use super::{Error::*, Result};

pub fn intros_one(frame: &mut Frame, name: &str) -> Result<()> {
    let goal = frame.goal.clone();
    match goal.as_ref() {
        Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) => {
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
        while let Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name,
        }) = frame.goal.clone().as_ref()
        {
            let name = if let Some(name) = hint_name {
                frame.engine.generate_name(name)
            } else {
                frame.engine.generate_name("H")
            };
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

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_fail;

    const GOAL: &str = "∀ a b: ℤ, a < b";

    #[test]
    fn duplicate_hyp() {
        run_interactive_to_fail(GOAL, "intros x", "intros x");
    }

    #[test]
    fn intros_bad_arg() {
        run_interactive_to_fail(GOAL, "", "intros x 5");
        run_interactive_to_fail(GOAL, "", "intros -2");
        run_interactive_to_fail(GOAL, "", "intros (rewrite x)");
    }
}
