use super::Result;
use crate::interactive::Frame;

pub(crate) fn chain(frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let mut frames = vec![frame];
    for arg in args {
        let mut arg = arg.as_str();
        if let Some(a) = arg.strip_prefix('(') {
            if let Some(a) = a.strip_suffix(')') {
                arg = a;
            }
        }
        frames = frames
            .into_iter()
            .map(|x| x.run_tactic(arg))
            .collect::<Result<Vec<Vec<_>>>>()?
            .into_iter()
            .flat_map(|x| x.into_iter())
            .collect();
    }
    Ok(frames)
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn or_destruct() {
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
