use serde::__private::de;

use super::{next_arg, next_arg_constant, rewrite::replace_term, Result};
use crate::{
    app, app_ref,
    brain::{Term, TermRef},
    interactive::{tactic::rewrite::replace_term_in_frame, Frame},
    library::prelude::{cons, list, nil},
};

fn eat_paren(mut x: &str) -> &str {
    if let Some(a) = x.strip_prefix('(') {
        if let Some(a) = a.strip_suffix(')') {
            x = a;
        }
    }
    x
}

pub(crate) fn chain<'a>(frame: Frame, args: impl Iterator<Item = &'a str>) -> Result<Vec<Frame>> {
    let mut frames = vec![frame];
    for arg in args {
        let arg = eat_paren(arg);
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

pub(crate) fn destruct<'a>(
    frame: Frame,
    args: impl Iterator<Item = &'a str>,
) -> Result<Vec<Frame>> {
    let args = &mut args.peekable();
    let tactic_name = "destruct";
    let hyp = next_arg(args, tactic_name)?;

    if next_arg_constant(args, tactic_name, "with").is_err() {
        return destruct_varible(frame, hyp);
    };
    let lem = next_arg(args, tactic_name)?;
    let var = if args.peek().is_none() {
        hyp
    } else {
        next_arg_constant(args, tactic_name, "to")?;
        eat_paren(next_arg(args, tactic_name)?)
    };
    frame.run_tactic(&format!(
        "chain (apply ({} {})) (remove_hyp {}) (intros {})",
        lem, hyp, hyp, var
    ))
}

fn destruct_varible(frame: Frame, arg: &str) -> Result<Vec<Frame>> {
    for (pos, hyp) in frame.hyps.iter().enumerate() {
        if hyp.name == arg {
            if let Term::App { func, op: ty } = hyp.ty.clone().as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "list" {
                        let term_of_varible = frame.engine.parse_text(arg)?;
                        let mut nil_frame = frame.clone();
                        destruct_varible_with_term(
                            &mut nil_frame,
                            term_of_varible.clone(),
                            app_ref!(nil(), ty),
                            pos + 1,
                        );
                        let mut cons_frame = frame.clone();
                        let x = cons_frame.engine.generate_name("x");
                        let l = cons_frame.engine.generate_name("l");
                        cons_frame.add_hyp_with_name_in_index(&x, ty.clone(), pos + 1)?;
                        cons_frame.add_hyp_with_name_in_index(&l, app_ref!(list(), ty), pos + 2)?;
                        let replace = cons_frame
                            .engine
                            .parse_text(&format!("({}) :: ({})", x, l))?;
                        destruct_varible_with_term(
                            &mut cons_frame,
                            term_of_varible,
                            replace,
                            pos + 3,
                        );
                        nil_frame.remove_hyp_with_index(pos)?;
                        cons_frame.remove_hyp_with_index(pos)?;
                        return Ok(vec![cons_frame, nil_frame]);
                    }
                }
            }
        }
    }
    Err(super::Error::BadArg {
        tactic_name: "destruct".to_string(),
        arg: "no option".to_string(),
    })
}

fn destruct_varible_with_term(
    frame: &mut Frame,
    term_of_varible: TermRef,
    replace: TermRef,
    start_index: usize,
) {
    for i in start_index..frame.hyps.len() {
        let hyp = &mut frame.hyps[i];
        hyp.ty = replace_term(
            hyp.ty.clone(),
            term_of_varible.clone(),
            replace.clone(),
            &mut None,
        );
        frame
            .engine
            .update_term_of_axiom(hyp.name.as_str(), hyp.ty.clone());
    }
    frame.goal = replace_term(frame.goal.clone(), term_of_varible, replace, &mut None);
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{
        run_interactive, run_interactive_to_end, run_interactive_to_fail, EngineLevel,
    };

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
    #[test]
    fn destruct_list_varible_then_destruct_and() {
        run_interactive_to_end(
            "∀ l: list ℤ, head 0 l = 2 ∧ tail l = [3] -> l = [2, 3]",
            r#"
                intros
                destruct l
                Switch 1
                destruct H with (and_ind ? ?) to (H_l H_r)
        "#,
        )
    }
    #[test]
    fn destruct_panic() {
        run_interactive(
            r#"∀ l: list char,
        ∀ n: ℤ,
          cnt '(' l = n
                ∧ cnt ')' l = n
                    ∧ ∀ i: ℤ,
                        0 < i → i ≤ |l| → cnt ')' (firstn l i) ≤ cnt '(' (firstn l i)"#,
            r#"
                intros
                destruct l
                "#,
            EngineLevel::Full,
        );
    }
}
