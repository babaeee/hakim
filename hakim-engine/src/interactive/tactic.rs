use crate::brain::{self, TermRef};

mod rewrite;
pub(crate) use rewrite::{replace, rewrite};

mod ring;
pub(crate) use ring::ring;

mod lia;
pub(crate) use lia::lia;

mod intros;
pub(crate) use intros::intros;

mod apply;
pub(crate) use apply::apply;

mod hyps;
pub(crate) use hyps::{add_hyp, remove_hyp};

mod auto_set;
pub(crate) use auto_set::auto_set;

mod chain;
pub(crate) use chain::{chain, destruct};

mod assumption;
pub(crate) use assumption::assumption;

#[derive(Debug)]
pub enum Error {
    UnknownTactic(String),
    UnknownHyp(String),
    BadHyp(&'static str, TermRef),
    BadGoal(&'static str),
    BadArgCount { tactic_name: String },
    BadArg { tactic_name: String, arg: String },
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

pub(crate) fn next_arg(
    args: &mut impl Iterator<Item = String>,
    tactic_name: &'static str,
) -> Result<String> {
    let arg = args.next().ok_or(BadArgCount {
        tactic_name: tactic_name.to_string(),
    })?;
    Ok(arg)
}

pub(crate) fn next_arg_constant(
    args: &mut impl Iterator<Item = String>,
    tactic_name: &'static str,
    expected: &'static str,
) -> Result<()> {
    let v = next_arg(args, tactic_name)?;
    if v != expected {
        return Err(BadArg {
            arg: v,
            tactic_name: tactic_name.to_string(),
        });
    }
    Ok(())
}

pub(crate) fn deny_arg(
    mut args: impl Iterator<Item = String>,
    tactic_name: &'static str,
) -> Result<()> {
    if args.next().is_some() {
        return Err(BadArgCount {
            tactic_name: tactic_name.to_string(),
        });
    }
    Ok(())
}

pub(crate) fn get_one_arg(
    mut args: impl Iterator<Item = String>,
    tactic_name: &'static str,
) -> Result<String> {
    let arg1 = next_arg(&mut args, tactic_name)?;
    deny_arg(args, tactic_name)?;
    Ok(arg1)
}
