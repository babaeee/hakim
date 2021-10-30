use crate::brain::{self, TermRef};

mod rewrite;
pub use rewrite::rewrite;

mod ring;
pub use ring::ring;

mod intros;
pub use intros::intros;

mod apply;
pub use apply::apply;

mod hyps;
pub use hyps::{add_hyp, remove_hyp};

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
    CanNotFindInstance(usize, TermRef),
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
