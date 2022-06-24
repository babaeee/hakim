use crate::{
    app_ref,
    brain::{
        infer::{type_of_and_infer, InferResults},
        type_of, Term, TermRef,
    },
    interactive::Frame,
    library::prelude::eq,
    parser::{fix_wild_scope, BinOp, InferGenerator},
    Abstraction,
};

use super::{deny_arg, get_one_arg, next_arg, next_arg_constant, Error::*, Result};

fn replace_term(
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
    if let Some((l, op, r)) = BinOp::detect(&exp) {
        if DUPLICATORS.contains(&op) {
            let mut infer_cnt = InferGenerator::default();
            let l = replace_term(l, find.clone(), replace.clone(), which);
            let r = replace_term(r, find, replace, which);
            let result = op.run_on_term(&mut infer_cnt, l, r);
            let n = infer_cnt.0;
            let result = fix_wild_scope(result, n);
            let mut infers = InferResults::new(n);
            let ty = type_of_and_infer(result.clone(), &mut infers).unwrap();
            type_of_and_infer(ty, &mut infers).unwrap();
            let result = infers.fill(result);
            return result;
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

pub fn rewrite<'a>(mut frame: Frame, args: impl Iterator<Item = &'a str>) -> Result<Vec<Frame>> {
    let mut args = args.peekable();
    let is_reverse = args.peek() == Some(&"<-");
    if is_reverse {
        args.next();
    }
    let exp = &get_one_arg(args, "rewrite")?;
    let term = frame.engine.calc_type(exp)?;
    let [op1, op2, _] = get_eq_params(&term).ok_or(BadHyp("rewrite expect eq but got", term))?;
    let goal = frame.goal.clone();
    frame.goal = if is_reverse {
        replace_term(goal, op2, op1, &mut None)
    } else {
        replace_term(goal, op1, op2, &mut None)
    };
    Ok(vec![frame])
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
    let find = frame.engine.parse_text(find)?;
    next_arg_constant(&mut args, "replace", "with")?;
    let replace = next_arg(&mut args, "replace")?;
    let replace = frame.engine.parse_text(replace)?;
    let mut proof_eq = frame.clone();
    proof_eq.goal = build_eq_term(find.clone(), replace.clone())?;
    let mut after_replace = frame;
    if args.peek().is_some() {
        next_arg_constant(&mut args, "replace", "in")?;
        let hyp_name = next_arg(&mut args, "replace")?;
        let hyp = after_replace.remove_hyp_with_name(hyp_name)?.ty;
        after_replace.add_hyp_with_name(hyp_name, replace_term(hyp, find, replace, &mut which))?;
        deny_arg(args, "replace")?;
    } else {
        after_replace.goal = replace_term(after_replace.goal, find, replace, &mut which);
    }
    Ok(vec![after_replace, proof_eq])
}

fn build_eq_term(t1: TermRef, t2: TermRef) -> Result<TermRef> {
    let ty = type_of(t1.clone())?;
    let r = app_ref!(eq(), ty, t1, t2);
    type_of(r.clone())?;
    Ok(r)
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive, run_interactive_to_end, EngineLevel};

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
}
