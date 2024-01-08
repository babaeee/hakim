use crate::brain::{self, TermRef};

mod rewrite;
pub(crate) use rewrite::{replace, rewrite};

mod unfold;
pub(crate) use unfold::unfold;

mod lia;
pub(crate) use lia::lia;

mod lra;
pub(crate) use lra::lra;

mod intros;
pub(crate) use intros::intros;

mod apply;
pub(crate) use apply::apply;
pub use apply::FindInstance;

mod hyps;
pub(crate) use hyps::{add_from_lib, add_hyp, remove_hyp, revert_hyp as revert};

mod auto_set;
pub(crate) use auto_set::auto_set;

mod auto_list;
pub(crate) use auto_list::auto_list;

mod chain;
pub(crate) use chain::{chain, destruct};

mod assumption;
pub(crate) use assumption::assumption;

mod z3_auto;
pub use z3_auto::{z3_auto, Z3_TIMEOUT};

#[derive(Debug)]
pub enum Error {
    UnknownTactic(String),
    DisabledTactic(String),
    UnknownHyp(String),
    BadHyp(&'static str, TermRef),
    BadGoal(&'static str),
    BadArgCount { tactic_name: String },
    BadArg { tactic_name: String, arg: String },
    BrainError(brain::Error),
    CanNotSolve(&'static str),
    CanNotUndo,
    CanNotRedo,
    EmptyTactic,
    InvalidGoalNumber { i: usize, n: usize },
    HypIsFromLib(String),
    EngineError(super::Error),
    CanNotFindInstance(Box<FindInstance>),
    ContextDependOnHyp(String, TermRef),
    TermIsNotType(TermRef),
    MismatchedParen,
    Z3State(String),
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

pub(crate) fn next_arg<'a>(
    args: &mut impl Iterator<Item = &'a str>,
    tactic_name: &'static str,
) -> Result<&'a str> {
    let arg = args.next().ok_or(BadArgCount {
        tactic_name: tactic_name.to_string(),
    })?;
    Ok(arg)
}

pub(crate) fn next_arg_constant<'a>(
    args: &mut impl Iterator<Item = &'a str>,
    tactic_name: &'static str,
    expected: &'static str,
) -> Result<()> {
    let v = next_arg(args, tactic_name)?;
    if v != expected {
        return Err(BadArg {
            arg: v.to_string(),
            tactic_name: tactic_name.to_string(),
        });
    }
    Ok(())
}

pub(crate) fn deny_arg<'a>(
    mut args: impl Iterator<Item = &'a str>,
    tactic_name: &'static str,
) -> Result<()> {
    if args.next().is_some() {
        return Err(BadArgCount {
            tactic_name: tactic_name.to_string(),
        });
    }
    Ok(())
}

pub(crate) fn get_one_arg<'a>(
    mut args: impl Iterator<Item = &'a str>,
    tactic_name: &'static str,
) -> Result<&'a str> {
    let arg1 = next_arg(&mut args, tactic_name)?;
    deny_arg(args, tactic_name)?;
    Ok(arg1)
}
