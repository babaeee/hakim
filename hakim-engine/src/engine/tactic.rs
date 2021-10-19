use crate::{
    brain::{self, create_infer_vec, match_and_infer, match_term, subst, Term, TermRef},
    term_ref,
};

use super::{
    interactive::{InteractiveFrame, InteractiveSession},
    Engine,
};

#[derive(Debug)]
pub enum Error {
    UnknownTactic(String),
    BadHyp(&'static str, TermRef),
    BadGoal(&'static str),
    BrainError(brain::Error),
    EngineError(super::Error),
}

impl From<super::Error> for Error {
    fn from(e: super::Error) -> Self {
        EngineError(e)
    }
}

impl From<brain::Error> for Error {
    fn from(e: brain::Error) -> Self {
        BrainError(e)
    }
}

use Error::*;

pub fn intros(engine: &mut Engine, frame: &mut InteractiveFrame, name: &str) -> Result<(), Error> {
    let goal = &frame.goal;
    match goal.as_ref() {
        Term::Forall { var_ty, body } => {
            engine.add_axiom_with_term(name, var_ty.clone())?;
            frame.hyps.insert(name.to_string(), var_ty.clone());
            frame.goal = subst(body.clone(), term_ref!(axiom name, var_ty));
            Ok(())
        }
        _ => Err(BadGoal("intros expects forall")),
    }
}

pub fn apply(session: &mut InteractiveSession, exp: &str) -> Result<(), Error> {
    let term = session.engine.calc_type(exp)?;
    match_term(term, session.current_frame().goal.clone())?;
    session.solve_goal();
    Ok(())
}

pub fn rewrite(engine: &Engine, frame: &mut InteractiveFrame, exp: &str) -> Result<(), Error> {
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

    let term = engine.calc_type(exp)?;
    let eq_pat = engine.parse_text("eq _2 _0 _1")?;
    let mut infers = create_infer_vec(3);
    match_and_infer(term.clone(), eq_pat, &mut infers)
        .map_err(|_| BadHyp("rewrite expect eq but got", term))?;
    frame.goal = replace_term(frame.goal.clone(), infers[0].clone(), infers[1].clone());
    Ok(())
}
