#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UniOp {
    Neg,
    Not,
}

use std::fmt::{Display, Formatter};

use UniOp::*;

use crate::{
    app_ref,
    brain::{Term, TermRef},
    library, term_ref,
};

use super::{binop::BinOp, InferGenerator, PrecLevel};

impl Display for UniOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str(match self {
            Neg => "-",
            Not => "~",
        })
    }
}

impl UniOp {
    // Source: https://coq.inria.fr/library/Coq.Init.Notations.html
    pub fn prec(&self) -> PrecLevel {
        PrecLevel(match self {
            Neg => 35,
            Not => 75,
        })
    }

    pub fn run_on_term(&self, _: &mut InferGenerator, t: TermRef) -> TermRef {
        match self {
            Not => term_ref!(forall t, library::prelude::false_ty()),
            Neg => app_ref!(
                library::prelude::minus(),
                library::prelude::z(),
                term_ref!(n 0),
                t
            ),
        }
    }

    pub fn from_str(op: &str) -> Option<Self> {
        Some(match op {
            "-" => Neg,
            "~" => Not,
            _ => return None,
        })
    }

    pub(crate) fn detect(term: &crate::brain::Term) -> Option<(Self, TermRef)> {
        if let Some((a, op, b)) = BinOp::detect(term) {
            match op {
                BinOp::Imply => {
                    if let Term::Axiom { unique_name, .. } = b.as_ref() {
                        if unique_name == "False" {
                            return Some((Not, a));
                        }
                    }
                }
                BinOp::Minus => {
                    if let Term::Number { value } = a.as_ref() {
                        if value == &0.into() {
                            return Some((Neg, b));
                        }
                    }
                }
                _ => (),
            }
        }
        None
    }
}
