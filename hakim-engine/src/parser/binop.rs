#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    And,
    App,
    Eq,
    Iff,
    Imply,
    Lt,
    Mult,
    Or,
    Plus,
}

#[derive(PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
    No,
    Comm,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        f.write_str(match self {
            And => "∧",
            App => " ",
            Eq => "=",
            Imply => "→",
            Lt => "<",
            Mult => "*",
            Or => "∨",
            Plus => "+",
            Iff => "↔",
        })
    }
}

use std::fmt::{Display, Formatter};

use Assoc::*;
use BinOp::*;

use crate::{
    app_ref,
    brain::{increase_foreign_vars, remove_unused_var},
    library::prelude::*,
    term_ref, Abstraction, Term, TermRef,
};

impl BinOp {
    pub fn level_left(&self) -> u8 {
        match self.assoc() {
            Left | Comm => self.prec(),
            No | Right => self.prec() - 1,
        }
    }

    pub fn level_right(&self) -> u8 {
        match self.assoc() {
            Right => self.prec(),
            No | Left | Comm => self.prec() - 1,
        }
    }

    pub fn prec(&self) -> u8 {
        match self {
            App => 0,
            Eq => 70,
            Imply => 99,
            Iff => 98,
            Lt => 70,
            Mult => 40,
            Plus => 50,
            Or => 85,
            And => 80,
        }
    }

    pub fn assoc(&self) -> Assoc {
        match self {
            App => Left,
            Eq => No,
            Iff => Comm,
            Imply => Right,
            Lt => No,
            Mult => Comm,
            Plus => Comm,
            Or => Comm,
            And => Comm,
        }
    }

    pub fn from_str(op: &str) -> Option<Self> {
        Some(match op {
            "∧" => And,
            "=" => Eq,
            "↔" => Iff,
            "→" => Imply,
            "<" => Lt,
            "*" => Mult,
            "∨" => Or,
            "+" => Plus,
            _ => return None,
        })
    }

    pub fn run_on_term(&self, infer_cnt: &mut usize, l: TermRef, r: TermRef) -> TermRef {
        match self {
            App => app_ref!(l, r),
            Eq => {
                let i = *infer_cnt;
                *infer_cnt += 1;
                let w = term_ref!(_ i);
                app_ref!(eq(), w, l, r)
            }
            Iff => app_ref!(iff(), l, r),
            Imply => term_ref!(forall l, increase_foreign_vars(r, 0)),
            Lt => app_ref!(lt(), l, r),
            Mult => app_ref!(mult(), l, r),
            Plus => app_ref!(plus(), l, r),
            Or => app_ref!(or(), l, r),
            And => app_ref!(and(), l, r),
        }
    }

    pub fn detect(t: &TermRef) -> Option<(TermRef, Self, TermRef)> {
        match t.as_ref() {
            Term::App { func, op: op2 } => match func.as_ref() {
                Term::App { func, op } => match func.as_ref() {
                    Term::App { func, op: _ } => match func.as_ref() {
                        Term::Axiom { ty: _, unique_name } if unique_name == "eq" => {
                            Some((op.clone(), BinOp::Eq, op2.clone()))
                        }
                        _ => None,
                    },
                    Term::Axiom { ty: _, unique_name } => match unique_name.as_str() {
                        "iff" => Some((op.clone(), BinOp::Iff, op2.clone())),
                        "plus" => Some((op.clone(), BinOp::Plus, op2.clone())),
                        "mult" => Some((op.clone(), BinOp::Mult, op2.clone())),
                        "lt" => Some((op.clone(), BinOp::Lt, op2.clone())),
                        "or" => Some((op.clone(), BinOp::Or, op2.clone())),
                        "and" => Some((op.clone(), BinOp::And, op2.clone())),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            },
            Term::Forall(Abstraction { body, var_ty }) => {
                let x = remove_unused_var(body, 0)?;
                Some((var_ty.clone(), BinOp::Imply, x))
            }
            _ => None,
        }
    }
}
