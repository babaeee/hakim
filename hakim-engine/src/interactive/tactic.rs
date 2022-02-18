use crate::brain::{self, TermRef};

mod rewrite;
pub(crate) use rewrite::rewrite;

mod ring;
pub(crate) use ring::ring;

mod intros;
pub(crate) use intros::intros;

mod apply;
pub(crate) use apply::apply;

mod hyps;
pub(crate) use hyps::{add_hyp, remove_hyp};

mod auto_set;
pub(crate) use auto_set::auto_set;

#[derive(Debug)]
pub enum Error {
    UnknownTactic(String),
    UnknownHyp(String),
    BadHyp(&'static str, TermRef),
    BadGoal(&'static str),
    BadArgCount {
        tactic_name: String,
        expected: usize,
        found: usize,
    },
    BadArg {
        tactic_name: String,
        arg: String,
    },
    BrainError(brain::Error),
    CanNotSolve(&'static str),
    CanNotUndo,
    EmptyTactic,
    EngineError(super::Error),
    CanNotFindInstance(FindInstance),
    ContextDependOnHyp(String, TermRef),
    TermIsNotType(TermRef),
}

impl Error {
    pub fn is_actionable(&self) -> bool {
        matches!(self, CanNotFindInstance(..))
    }
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

use self::apply::FindInstance;

pub(crate) fn get_one_arg(
    mut args: impl Iterator<Item = String>,
    tactic_name: &str,
) -> Result<String> {
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
