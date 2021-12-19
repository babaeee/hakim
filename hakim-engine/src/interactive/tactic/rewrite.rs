use crate::{
    brain::{Term, TermRef},
    interactive::Frame,
    Abstraction,
};

use super::{get_one_arg, Error::*, Result};

fn replace_term(exp: TermRef, find: TermRef, replace: TermRef) -> TermRef {
    fn for_abs(
        Abstraction {
            var_ty,
            body,
            hint_name,
        }: &Abstraction,
        find: TermRef,
        replace: TermRef,
    ) -> Abstraction {
        let var_ty = replace_term(var_ty.clone(), find.clone(), replace.clone());
        let body = replace_term(body.clone(), find, replace);
        let hint_name = hint_name.clone();
        Abstraction {
            var_ty,
            body,
            hint_name,
        }
    }
    if exp == find {
        return replace;
    }
    match exp.as_ref() {
        Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Var { .. }
        | Term::Wild { .. }
        | Term::Number { .. } => exp,
        Term::Forall(a) => TermRef::new(Term::Forall(for_abs(a, find, replace))),
        Term::Fun(a) => TermRef::new(Term::Fun(for_abs(a, find, replace))),
        Term::App { func, op } => TermRef::new(Term::App {
            func: replace_term(func.clone(), find.clone(), replace.clone()),
            op: replace_term(op.clone(), find, replace),
        }),
    }
}

pub fn get_eq_params(term: &TermRef) -> Option<[TermRef; 3]> {
    if let Term::App { func, op: op2 } = term.as_ref() {
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

pub fn rewrite(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let mut args = args.peekable();
    let is_reverse = args.peek() == Some(&"<-".to_string());
    if is_reverse {
        args.next();
    }
    let exp = &get_one_arg(args, "rewrite")?;
    let term = frame.engine.calc_type(exp)?;
    let [op1, op2, _] = get_eq_params(&term).ok_or(BadHyp("rewrite expect eq but got", term))?;
    let goal = frame.goal.clone();
    frame.goal = if is_reverse {
        replace_term(goal, op2, op1)
    } else {
        replace_term(goal, op1, op2)
    };
    Ok(vec![frame])
}
