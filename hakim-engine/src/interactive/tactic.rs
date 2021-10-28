use crate::brain::{self, TermRef};

use crate::interactive::Frame;

mod rewrite;
pub use rewrite::rewrite;

mod ring;
pub use ring::ring;

mod intros;
pub use intros::intros;

mod apply;
pub use apply::apply;

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

pub fn add_hyp(mut frame: Frame, args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let exp = get_one_arg(args, "intros")?;
    let term = frame.engine.parse_text(&exp)?;
    let mut frame2 = frame.clone();
    frame.add_hyp_with_name(&frame.engine.generate_name("H"), term.clone())?;
    frame2.goal = term;
    Ok(vec![frame, frame2])
}
