use crate::brain::{create_infer_vec, match_and_infer, Term, TermRef};
use crate::engine::interactive::InteractiveSnapshot;

use super::super::Engine;
use super::{get_one_arg, Error::*, Result};

fn replace_term(exp: TermRef, find: TermRef, replace: TermRef) -> TermRef {
    if exp == find {
        return replace;
    }
    match exp.as_ref() {
        Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Var { .. }
        | Term::Wild { .. }
        | Term::Number { .. } => exp,
        Term::Forall { var_ty, body } => TermRef::new(Term::Forall {
            var_ty: replace_term(var_ty.clone(), find.clone(), replace.clone()),
            body: replace_term(body.clone(), find, replace),
        }),
        Term::App { func, op } => TermRef::new(Term::App {
            func: replace_term(func.clone(), find.clone(), replace.clone()),
            op: replace_term(op.clone(), find, replace),
        }),
    }
}

pub fn get_eq_params(engine: &Engine, term: TermRef) -> Option<[TermRef; 2]> {
    let eq_pat = engine.parse_text("eq _2 _0 _1").ok()?;
    let mut infers = create_infer_vec(3);
    match_and_infer(term.clone(), eq_pat, &mut infers).ok()?;
    let mut iter = infers.into_iter();
    Some([iter.next().unwrap(), iter.next().unwrap()])
}

pub fn rewrite(
    snapshot: &InteractiveSnapshot,
    args: impl Iterator<Item = String>,
) -> Result<InteractiveSnapshot> {
    let exp = &get_one_arg(args, "rewrite")?;
    let mut snapshot = snapshot.clone();
    let term = snapshot.engine.calc_type(exp)?;
    let [op1, op2] = get_eq_params(&snapshot.engine, term.clone())
        .ok_or(BadHyp("rewrite expect eq but got", term))?;
    let goal = snapshot.current_frame().goal.clone();
    snapshot.current_frame().goal = replace_term(goal, op1, op2);
    Ok(snapshot)
}
