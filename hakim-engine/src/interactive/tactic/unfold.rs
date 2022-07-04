use super::{next_arg, Result};
use crate::{brain::fill_axiom, interactive::Frame, term_ref};

pub(crate) fn unfold<'a>(
    mut frame: Frame,
    args: impl Iterator<Item = &'a str>,
) -> Result<Vec<Frame>> {
    let args = &mut args.peekable();
    let tactic_name = "unfold";
    let def = next_arg(args, tactic_name)?;
    let body = frame.engine.body_of_definition(def)?;
    frame.goal = fill_axiom(frame.goal, |x, y, _| {
        if def == x {
            body.clone()
        } else {
            term_ref!(axiom x, y)
        }
    });
    Ok(vec![frame])
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn simple() {
        run_interactive_to_end(
            "∀ x: ℤ, prime x -> 1 < x ∧ (∀ y: ℤ, 0 < y -> y | x -> y = 1 ∨ y = x)",
            r#"
            unfold prime
            intros
            assumption
        "#,
        )
    }
}
