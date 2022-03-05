use super::{next_arg, next_arg_constant, Result};
use crate::interactive::Frame;

fn eat_paren(mut x: &str) -> String {
    if let Some(a) = x.strip_prefix('(') {
        if let Some(a) = a.strip_suffix(')') {
            x = a;
        }
    }
    x.to_string()
}

pub(crate) fn chain(frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let mut frames = vec![frame];
    for arg in args {
        let arg = eat_paren(&arg);
        frames = frames
            .into_iter()
            .map(|x| x.run_tactic(&arg))
            .collect::<Result<Vec<Vec<_>>>>()?
            .into_iter()
            .flat_map(|x| x.into_iter())
            .collect();
    }
    Ok(frames)
}

pub(crate) fn destruct(frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let args = &mut args.peekable();
    let tactic_name = "destruct";
    let hyp = next_arg(args, tactic_name)?;
    next_arg_constant(args, tactic_name, "with")?;
    let lem = next_arg(args, tactic_name)?;
    let var = if args.peek().is_none() {
        hyp.clone()
    } else {
        next_arg_constant(args, tactic_name, "to")?;
        eat_paren(&next_arg(args, tactic_name)?)
    };
    frame.run_tactic(&format!(
        "chain (apply ({} {})) (remove_hyp {}) (intros {})",
        lem, hyp, hyp, var
    ))
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn and_destruct() {
        run_interactive_to_end(
            "∀ A B: U, A ∧ B -> B",
            r#"
            intros A B H
            destruct H with (and_ind ? ?) to (H_l H_r)
            apply H_r
        "#,
        )
    }

    #[test]
    fn or_destruct() {
        run_interactive_to_end(
            "∀ A B: U, A ∨ B -> (A -> B) -> B",
            r#"
            intros A B P Q
            destruct P with (or_ind ? ?)
            apply P
            apply (Q P)
        "#,
        )
    }

    #[test]
    fn or_destruct_manual() {
        run_interactive_to_end(
            "∀ A B: U, A ∨ B -> (A -> B) -> B",
            r#"
            intros A B P Q
            chain (apply (or_ind ? ? P)) (remove_hyp P) (intros P)
            apply P
            apply (Q P)
        "#,
        )
    }
}
