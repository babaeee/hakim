use super::{get_one_arg, Error, Result};
use crate::{
    brain::{type_of, Term},
    interactive::Frame,
};

pub fn add_hyp(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let exp = get_one_arg(args, "add_hyp")?;
    let term = frame.engine.parse_text(&exp)?;
    let ty = type_of(term.clone())?;
    if !matches!(ty.as_ref(), Term::Universe { .. }) {
        return Err(Error::TermIsNotType(term));
    }
    let mut frame2 = frame.clone();
    frame.add_hyp_with_name(&frame.engine.generate_name("H"), term.clone())?;
    frame2.goal = term;
    Ok(vec![frame, frame2])
}

pub fn remove_hyp(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let exp = get_one_arg(args, "remove_hyp")?;
    frame.remove_hyp_with_name(exp)?;
    Ok(vec![frame])
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

    #[test]
    fn success_add_hyp() {
        run_interactive_to_end(
            "forall a b c d: ℤ, a < b -> c < d -> a + c < b + d",
            r#"
            intros a
            intros b
            intros c
            intros d
            intros a_lt_b
            intros c_lt_d
            add_hyp (a + c < b + c)
            apply (lt_plus_r a b c a_lt_b)
            add_hyp (b + c < b + d)
            apply (lt_plus_l c d b c_lt_d)
            apply (lt_trans (a+c) (b+c) (b+d) H H0)
            "#,
        );
    }

    #[test]
    fn dont_remove_dependent() {
        run_interactive_to_fail("∀ a: ℤ, a < a + 5", "intros a", "remove_hyp a");
    }

    #[test]
    fn dont_add_non_type() {
        run_interactive_to_fail("False", "", "add_hyp 2");
    }

    #[test]
    fn remove_hyp_reuse_name() {
        run_interactive_to_end(
            "False -> False -> False",
            r#"
            intros fp
            remove_hyp fp
            intros fp
            apply fp
            "#,
        );
    }
}
