use crate::{
    brain::{self, match_term, subst, Term, TermRef},
    term_ref,
};

use super::interactive::InteractiveSnapshot;

mod rewrite;
pub use rewrite::rewrite;

mod ring;
pub use ring::ring;

#[derive(Debug)]
pub enum Error {
    UnknownTactic(String),
    BadHyp(&'static str, TermRef),
    BadGoal(&'static str),
    BadArgCount {
        tactic_name: String,
        expected: usize,
        found: usize,
    },
    BrainError(brain::Error),
    CanNotSolve(&'static str),
    CanNotUndo,
    EmptyTactic,
    EngineError(super::Error),
}

pub type Result<T> = std::result::Result<T, Error>;

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

pub fn get_one_arg(mut args: impl Iterator<Item = String>, tactic_name: &str) -> Result<String> {
    let arg1 = args.next().ok_or(BadArgCount {
        tactic_name: tactic_name.to_string(),
        expected: 1,
        found: 0,
    })?;
    let c = args.count();
    if c > 0 {
        return Err(BadArgCount {
            tactic_name: tactic_name.to_string(),
            expected: 1,
            found: c + 1,
        });
    }
    Ok(arg1)
}

pub fn intros(
    snapshot: &InteractiveSnapshot,
    args: impl Iterator<Item = String>,
) -> Result<InteractiveSnapshot> {
    let name = get_one_arg(args, "intros")?;
    let mut snapshot = snapshot.clone();
    let goal = snapshot.current_frame().goal.clone();
    match goal.as_ref() {
        Term::Forall { var_ty, body } => {
            snapshot.add_hyp_with_name(&name, var_ty.clone())?;
            snapshot.current_frame().goal = subst(body.clone(), term_ref!(axiom name, var_ty));
            Ok(snapshot)
        }
        _ => Err(BadGoal("intros expects forall")),
    }
}

pub fn apply(
    session: &InteractiveSnapshot,
    args: impl Iterator<Item = String>,
) -> Result<InteractiveSnapshot> {
    let exp = &get_one_arg(args, "apply")?;
    let mut session = session.clone();
    let term = session.engine.calc_type(exp)?;
    match_term(term, session.current_frame().goal.clone())?;
    session.solve_goal();
    Ok(session)
}
