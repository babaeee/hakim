use std::collections::HashSet;

use crate::{
    brain::{Term, TermRef},
    interactive::Frame,
    parser::BinOp,
    Abstraction,
};

use super::{deny_arg, get_one_arg, next_arg, next_arg_constant, Error::*, Result};

pub fn replace_term(
    exp: TermRef,
    find: TermRef,
    replace: TermRef,
    which: &mut Option<isize>,
) -> TermRef {
    fn for_abs(
        Abstraction {
            var_ty,
            body,
            hint_name,
        }: &Abstraction,
        find: TermRef,
        replace: TermRef,
        which: &mut Option<isize>,
    ) -> Abstraction {
        let var_ty = replace_term(var_ty.clone(), find.clone(), replace.clone(), which);
        let body = replace_term(body.clone(), find, replace, which);
        let hint_name = hint_name.clone();
        Abstraction {
            var_ty,
            body,
            hint_name,
        }
    }
    if exp == find {
        match which {
            Some(x) => {
                *x -= 1;
                if *x == 0 {
                    return replace;
                }
            }
            None => return replace,
        }
    }
    const DUPLICATORS: &[BinOp] = &[BinOp::Le, BinOp::Iff];
    if let Some((l, op, r, ty)) = BinOp::detect_custom(&exp, &HashSet::new()) {
        if DUPLICATORS.contains(&op) {
            let l = replace_term(l, find.clone(), replace.clone(), which);
            let r = replace_term(r, find, replace, which);
            return op.run_on_term_with_ty(l, r, || ty.unwrap());
        }
    }
    match exp.as_ref() {
        Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Var { .. }
        | Term::Wild { .. }
        | Term::Number { .. } => exp,
        Term::Forall(a) => TermRef::new(Term::Forall(for_abs(a, find, replace, which))),
        Term::Fun(a) => TermRef::new(Term::Fun(for_abs(a, find, replace, which))),
        Term::App { func, op } => TermRef::new(Term::App {
            func: replace_term(func.clone(), find.clone(), replace.clone(), which),
            op: replace_term(op.clone(), find, replace, which),
        }),
    }
}

pub fn get_eq_params(term: &Term) -> Option<[TermRef; 3]> {
    if let Term::App { func, op: op2 } = term {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "eq" {
                        return Some([op1.clone(), op2.clone(), ty.clone()]);
                    }
                }
            }
        }
    }
    None
}
pub fn replace_term_in_frame(
    frame: &mut Frame,
    exp_index: usize,
    find: TermRef,
    replace: TermRef,
    which: &mut Option<isize>,
) -> Option<()> {
    // exp is goal or hyp
    if exp_index != usize::MAX {
        let hyp = frame.hyps.get(exp_index)?.clone();
        let new_hyp = replace_term(hyp.ty.clone(), find, replace, which);
        if new_hyp == hyp.ty {
            return None;
        }
        if frame.remove_hyp_with_index(exp_index).is_err() {
            return None;
        }
        if frame.add_hyp_with_name(&hyp.name, new_hyp).is_err() {
            return None;
        }
    } else {
        let new_goal = replace_term(frame.goal.clone(), find, replace, which);
        if new_goal == frame.goal {
            return None;
        }
        frame.goal = new_goal;
    }
    Some(())
}
pub fn rewrite<'a>(mut frame: Frame, args: impl Iterator<Item = &'a str>) -> Result<Vec<Frame>> {
    let mut args = args.peekable();
    let is_reverse = args.peek() == Some(&"<-");
    if is_reverse {
        args.next();
    }
    let exp = &get_one_arg(args, "rewrite")?;
    let term = frame.engine.calc_type(exp)?;
    let [op1, op2, _] =
        get_eq_params(&(term)).ok_or_else(|| BadHyp("rewrite expect eq but got", term.clone()))?;
    let result = if is_reverse {
        replace_term_in_frame(&mut frame, usize::MAX, op2, op1, &mut None)
    } else {
        replace_term_in_frame(&mut frame, usize::MAX, op1, op2, &mut None)
    };
    match result {
        Some(()) => Ok(vec![frame]),
        None => Err(BadHyp("no rewrite option", term)),
    }
}

pub fn replace<'a>(frame: Frame, args: impl Iterator<Item = &'a str>) -> Result<Vec<Frame>> {
    let mut args = args.peekable();
    let mut which = None;
    if let Some(x) = args.peek() {
        if &x[..1] == "#" {
            let n: isize = x[1..].parse().map_err(|_| BadArg {
                arg: x.to_string(),
                tactic_name: "replace".to_string(),
            })?;
            which = Some(n);
            args.next();
        }
    }
    let find = next_arg(&mut args, "replace")?;
    next_arg_constant(&mut args, "replace", "with")?;
    let replace = next_arg(&mut args, "replace")?;
    let eq = format!("({}) = ({})", find, replace);
    let eq = frame.engine.parse_text(&eq)?;
    let mut proof_eq = frame.clone();
    proof_eq.goal = eq.clone();
    let mut after_replace = frame;

    if let Term::App { func, op: replace } = eq.as_ref() {
        if let Term::App { func: _, op: find } = func.as_ref() {
            let result = if args.peek().is_some() {
                next_arg_constant(&mut args, "replace", "in")?;
                let hyp_name = next_arg(&mut args, "replace")?;
                if let Some((i, _)) = after_replace
                    .hyps
                    .iter()
                    .enumerate()
                    .find(|(_, x)| x.name == hyp_name)
                {
                    deny_arg(args, "replace")?;
                    replace_term_in_frame(
                        &mut after_replace,
                        i,
                        find.clone(),
                        replace.clone(),
                        &mut which,
                    )
                } else {
                    None
                }
            } else {
                replace_term_in_frame(
                    &mut after_replace,
                    usize::MAX,
                    find.clone(),
                    replace.clone(),
                    &mut which,
                )
            };
            return match result {
                Some(_) => Ok(vec![after_replace, proof_eq]),
                None => Err(BadArg {
                    tactic_name: "replace".to_string(),
                    arg: "no change".to_string(),
                }),
            };
        }
    }
    unreachable!();
}
/*
fn build_eq_term(t1: TermRef, t2: TermRef) -> Result<TermRef> {
    let ty = type_of(t1.clone())?;
    let r = app_ref!(eq(), ty, t1, t2);
    type_of(r.clone())?;
    Ok(r)
}*/

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{
        run_interactive, run_interactive_to_end, run_interactive_to_fail, EngineLevel,
    };

    #[test]
    fn replace_hyp() {
        run_interactive_to_end(
            "∀ a: ℤ, a + a < 5 -> 2 * a < 5",
            r#"
            intros a hyp
            replace (a + a) with (2 * a) in hyp
            lia
            apply hyp
            "#,
        );
    }

    #[test]
    fn replace_goal() {
        run_interactive_to_end(
            "∀ a: ℤ, a + a < 5 -> 2 * a < 5",
            r#"
            intros a hyp
            replace (2 * a) with (a + a)
            lia
            apply hyp
            "#,
        );
    }

    #[test]
    fn replace_duplicators() {
        run_interactive_to_end(
            "∀ a: ℤ, a + a ≤ 5 <-> 2 * a ≤ 5",
            r#"
            intros a
            replace #1 (2 * a) with (a + a)
            lia
            chain (apply and_intro) (intros x) (apply x)
            "#,
        );
    }

    #[test]
    fn replace_sigma() {
        run_interactive(
            "∀ n: ℤ, 0 ≤ n → (Σ i in [0, n) |i|) = (Σ i in [0, n) i)",
            r#"
        intros n n_le_0
        replace #1 (Σ i in [0, n) |i|) with (5)
        "#,
            EngineLevel::Empty,
        );
    }

    #[test]
    #[ignore]
    fn replace_panic() {
        run_interactive(
            r#"∀ n: ℤ,
        0 ≤ n
          → 2 * (Σ i in [0, n + 1) i) = n * (n + 1)
              → 2 * (Σ i in [0, n + 1 + 1) i) = (n + 1) * (n + 1 + 1)"#,
            r#"replace #2 (0) with (2)"#,
            EngineLevel::Empty,
        );
    }
    #[test]
    fn panic_rewrite_member_set() {
        run_interactive_to_fail(
            "member_set [] = {1, 2, 3}",
            "",
            "replace (member_set []) with ({})",
        );
        /* it is generate (member_set ?4 [] = {}) for eq proof */
    }
    #[test]
    fn detect_infers_of_replace_obj() {
        run_interactive(
            r#"∀ A: U, 
            ∀ x y: set A, 
                x = {} ->
                    y = x -> 
                        y = {}"#,
            r#"
            intros
            replace #1 (x) with ({}) in H0
            assumption
            assumption
            "#,
            EngineLevel::Empty,
        );
    }
    #[test]
    fn rewrite_panic() {
        run_interactive("∀ l: list char,  ∀ n: ℤ, cnt '(' l = n ∧ cnt ')' l = n  ∧ ∀ i: ℤ,  0 < i → i ≤ |l| → cnt ')' (firstn l i) ≤ cnt '(' (firstn l i)",
        r#"
        intros
        add_from_lib cons_nil_case
        add_hyp cons_nil_case_ex := (cons_nil_case (char))
        add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (l))
        destruct cons_nil_case_ex_ex with (or_ind ? ?)
        destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (y y_property)
        destruct y_property with (ex_ind ? ?) to (a a_property)
        rewrite a_property"#,  EngineLevel::Full);
    }
}
