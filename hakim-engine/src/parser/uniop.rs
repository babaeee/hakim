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

    pub fn run_on_term(&self, infer_cnt: &mut InferGenerator, t: TermRef) -> TermRef {
        match self {
            Not => term_ref!(forall t, library::prelude::false_ty()),
            Neg => {
                let i = infer_cnt.generate();
                app_ref!(library::prelude::neg(), term_ref!(_ i), t)
            }
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
            if op == BinOp::Imply {
                if let Term::Axiom { unique_name, .. } = b.as_ref() {
                    if unique_name == "False" {
                        return Some((Not, a));
                    }
                }
            }
        }
        if let Term::App { func, op } = term {
            if let Term::App { func, op: _ } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "neg" {
                        return Some((Neg, op.clone()));
                    }
                }
            }
        }
        None
    }
}
