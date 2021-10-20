use crate::{
    brain::{self, match_term, subst, Term, TermRef},
    term_ref,
};

use super::{
    interactive::{InteractiveFrame, InteractiveSession},
    Engine,
};

mod rewrite;
pub use rewrite::rewrite;

mod ring;
pub use ring::ring;

#[derive(Debug)]
pub enum Error {
    UnknownTactic(String),
    BadHyp(&'static str, TermRef),
    BadGoal(&'static str),
    BrainError(brain::Error),
    EngineError(super::Error),
    CanNotSolve(&'static str),
}

type Result<T> = std::result::Result<T, Error>;

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

pub fn intros(engine: &mut Engine, frame: &mut InteractiveFrame, name: &str) -> Result<()> {
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

pub fn apply(session: &mut InteractiveSession, exp: &str) -> Result<()> {
    let term = session.engine.calc_type(exp)?;
    match_term(term, session.current_frame().goal.clone())?;
    session.solve_goal();
    Ok(())
}
