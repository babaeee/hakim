use crate::{
    app_ref,
    brain::{type_of, Term, TermRef},
    interactive::Frame,
    library::prelude::eq,
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
    let find = frame.engine.parse_text(&find)?;
    next_arg_constant(&mut args, "replace", "with")?;
    let replace = next_arg(&mut args, "replace")?;
    let replace = frame.engine.parse_text(&replace)?;
    let mut proof_eq = frame.clone();
    proof_eq.goal = build_eq_term(find.clone(), replace.clone())?;
    let mut after_replace = frame;
    if args.peek().is_some() {
        next_arg_constant(&mut args, "replace", "in")?;
        let hyp_name = next_arg(&mut args, "replace")?;
        let hyp = after_replace.remove_hyp_with_name(hyp_name.clone())?;
        after_replace.add_hyp_with_name(&hyp_name, replace_term(hyp, find, replace, &mut which))?;
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
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn replace_hyp() {
        run_interactive_to_end(
            "∀ a: ℤ, a + a < 5 -> 2 * a < 5",
            r#"
            intros a hyp
            replace (a + a) with (2 * a) in hyp
            ring
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
            ring
            apply hyp
            "#,
        );
    }
}
