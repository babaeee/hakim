use super::{get_one_arg, next_arg, next_arg_constant, Error, Result};
use crate::{
    brain::{fill_axiom, type_of, Abstraction, Term, TermRef},
    interactive::Frame,
    term_ref,
};

pub fn add_from_lib<'a>(
    mut frame: Frame,
    args: impl Iterator<Item = &'a str>,
) -> Result<Vec<Frame>> {
    let name = get_one_arg(args, "add_hyp")?;
    let ty = frame.engine.type_of_name(name)?;
    frame.hyps.push_back(crate::interactive::Hyp {
        ty,
        name: name.to_string(),
        from_lib: true,
    });
    Ok(vec![frame])
}

pub fn add_hyp<'a>(mut frame: Frame, args: impl Iterator<Item = &'a str>) -> Result<Vec<Frame>> {
    let mut args = args.peekable();
    let exp = next_arg(&mut args, "add_hyp")?;
    if args.peek().is_some() {
        next_arg_constant(&mut args, "add_hyp", ":=")?;
        let name = exp;
        let term = next_arg(&mut args, "add_hyp")?;
        let term = frame.engine.parse_text(term)?;
        let ty = type_of(term)?;
        frame.add_hyp_with_name(name, ty)?;
        return Ok(vec![frame]);
    }
    let term = frame.engine.parse_text(exp)?;
    let ty = type_of(term.clone())?;
    if !matches!(ty.as_ref(), Term::Universe { .. }) {
        return Err(Error::TermIsNotType(term));
    }
    let mut frame2 = frame.clone();
    frame.add_hyp_with_name(&frame.engine.generate_name("H"), term.clone())?;
    frame2.goal = term;
    Ok(vec![frame, frame2])
}

pub fn remove_hyp<'a>(mut frame: Frame, args: impl Iterator<Item = &'a str>) -> Result<Vec<Frame>> {
    let exp = get_one_arg(args, "remove_hyp")?;
    frame.remove_hyp_with_name(exp)?;
    Ok(vec![frame])
}

pub fn revert_hyp<'a>(mut frame: Frame, args: impl Iterator<Item = &'a str>) -> Result<Vec<Frame>> {
    let exp = get_one_arg(args, "revert")?;
    let ty = frame
        .get_hyp_by_name(exp)
        .ok_or_else(|| Error::UnknownHyp(exp.to_string()))?
        .ty
        .clone();
    let goal = frame.goal;
    let goal = fill_axiom(goal, |name, ty, depth| {
        if name == exp {
            term_ref!(v depth)
        } else {
            term_ref!(axiom name, ty)
        }
    });
    frame.goal = TermRef::new(Term::Forall(Abstraction {
        body: goal,
        var_ty: ty,
        hint_name: Some(exp.to_string()),
    }));
    frame.remove_hyp_with_name(exp)?;
    Ok(vec![frame])
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{
        run_interactive, run_interactive_to_end, run_interactive_to_fail, EngineLevel,
    };

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

    #[test]
    fn pose_style_add_hyp() {
        run_interactive_to_end(
            "∀ A: Universe, ∀ P: A → Universe, (∀ x: A, P x) → ∀ x: A, P x",
            r#"
            intros A P f x
            add_hyp H := (f x)
            apply H
            "#,
        );
    }

    #[test]
    fn add_hyp_and_add_from_lib() {
        run_interactive(
            "False",
            r#"
            add_from_lib le_multiply_positive
            add_hyp H := (le_multiply_positive (2))
            "#,
            EngineLevel::Full,
        );
    }

    #[test]
    fn from_lib() {
        run_interactive(
        "∀ A: U, ∀ P Q R S: set A, ∀ a: A, (a ∈ R -> a ∈ S) -> a ∈ R -> ((a ∈ S -> False) ∨ a ∈ Q) -> a ∈ Q",
        r#"
        intros A P Q R S a H1 H2 H3
        add_from_lib NNPP
        apply NNPP
    "#,
    EngineLevel::Full
    );
        run_interactive_to_fail("∀ A: U, ∀ P Q R S: set A, ∀ a: A, (a ∈ R -> a ∈ S) -> a ∈ R -> ((a ∈ S -> False) ∨ a ∈ Q) -> a ∈ Q",
    r#"
    intros A P Q R S a H1 H2 H3
    add_from_lib NNPP
    "#,
    "remove_hyp NNPP");
    }

    #[test]
    fn revert() {
        run_interactive(
            "∀ a b: ℤ, 0 ≤ a → 0 ≤ b → 0 ≤ a * b",
            r#"
            intros a b a_ge_0 b_ge_0
            revert b_ge_0
            revert b
            apply z_induction_simple
        "#,
            EngineLevel::Full,
        );
    }

    #[test]
    fn revert_preserve_name() {
        run_interactive_to_end(
            "2 = 3 -> 3 = 2",
            r#"
            intros eq_2_3
            revert eq_2_3
            intros
            apply eq_sym
            apply eq_2_3
        "#,
        );
    }
}
