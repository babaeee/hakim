#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    And,
    App,
    Divide,
    Eq,
    Iff,
    Imply,
    Included,
    Intersection,
    Inset,
    Lt,
    ModOf,
    Mult,
    Or,
    Plus,
    Setminus,
    Union,
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
            Divide => "|",
            Eq => "=",
            Iff => "↔",
            Imply => "→",
            Included => "⊆",
            Intersection => "∩",
            Inset => "∈",
            Lt => "<",
            ModOf => "mod",
            Mult => "*",
            Or => "∨",
            Plus => "+",
            Union => "∪",
            Setminus => "∖",
        })
    }
}

use std::fmt::{Display, Formatter};

use Assoc::*;
use BinOp::*;

use crate::{
    app_ref,
    brain::{increase_foreign_vars, increase_wild_scope, remove_unused_var},
    library::prelude::*,
    term_ref, Abstraction, Term, TermRef,
};

use super::ast::InferGenerator;

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
            And => 79,
            Divide => 70,
            Eq => 70,
            Imply => 99,
            Iff => 98,
            Included => 70,
            Intersection => 40,
            Inset => 70,
            Lt => 70,
            ModOf => 60,
            Mult => 40,
            Plus => 50,
            Or => 85,
            Union => 50,
            Setminus => 30,
        }
    }

    pub fn assoc(&self) -> Assoc {
        match self {
            And => Comm,
            App => Left,
            Divide => No,
            Eq => No,
            Iff => Comm,
            Imply => Right,
            Included => No,
            Intersection => Comm,
            Inset => No,
            Lt => No,
            ModOf => Left,
            Mult => Comm,
            Or => Comm,
            Plus => Comm,
            Union => Comm,
            Setminus => Comm,
        }
    }

    pub fn from_str(op: &str) -> Option<Self> {
        Some(match op {
            "∧" => And,
            "|" => Divide,
            "=" => Eq,
            "↔" => Iff,
            "→" => Imply,
            "⊆" => Included,
            "∩" => Intersection,
            "∈" => Inset,
            "<" => Lt,
            "mod" => ModOf,
            "*" => Mult,
            "∨" => Or,
            "+" => Plus,
            "∪" => Union,
            "∖" => Setminus,
            _ => return None,
        })
    }

    pub fn run_on_term(&self, infer_cnt: &mut InferGenerator, l: TermRef, r: TermRef) -> TermRef {
        match self {
            And => app_ref!(and(), l, r),
            App => app_ref!(l, r),
            Divide => app_ref!(divide(), l, r),
            Eq => {
                let i = infer_cnt.generate();
                let w = term_ref!(_ i);
                app_ref!(eq(), w, l, r)
            }
            Iff => app_ref!(
                and(),
                term_ref!(forall l, increase_wild_scope(increase_foreign_vars(r.clone(), 0))),
                term_ref!(forall r, increase_wild_scope(increase_foreign_vars(l, 0)))
            ),
            Imply => term_ref!(forall l, increase_foreign_vars(r, 0)),
            Included => {
                let i = infer_cnt.generate();
                let w = term_ref!(_ i);
                app_ref!(included(), w, l, r)
            }
            Intersection => {
                let i = infer_cnt.generate();
                let w = term_ref!(_ i);
                app_ref!(intersection(), w, l, r)
            }
            Inset => {
                let i = infer_cnt.generate();
                let w = term_ref!(_ i);
                app_ref!(inset(), w, l, r)
            }
            Lt => app_ref!(lt(), l, r),
            ModOf => app_ref!(mod_of(), l, r),
            Mult => app_ref!(mult(), l, r),
            Or => app_ref!(or(), l, r),
            Plus => app_ref!(plus(), l, r),
            Union => {
                let i = infer_cnt.generate();
                let w = term_ref!(_ i);
                app_ref!(union(), w, l, r)
            }
            Setminus => {
                let i = infer_cnt.generate();
                let w = term_ref!(_ i);
                app_ref!(setminus(), w, l, r)
            }
        }
    }

    pub fn detect(t: &Term) -> Option<(TermRef, Self, TermRef)> {
        Some(match t {
            Term::App { func, op: op2 } => match func.as_ref() {
                Term::App { func, op } => match func.as_ref() {
                    Term::App { func, op: _ } => match func.as_ref() {
                        Term::Axiom { ty: _, unique_name } => match unique_name.as_str() {
                            "eq" => (op.clone(), BinOp::Eq, op2.clone()),
                            "inset" => (op.clone(), BinOp::Inset, op2.clone()),
                            "included" => (op.clone(), BinOp::Included, op2.clone()),
                            "intersection" => (op.clone(), BinOp::Intersection, op2.clone()),
                            "union" => (op.clone(), BinOp::Union, op2.clone()),
                            "setminus" => (op.clone(), BinOp::Setminus, op2.clone()),
                            _ => return None,
                        },
                        _ => return None,
                    },
                    Term::Axiom { ty: _, unique_name } => match unique_name.as_str() {
                        "divide" => (op.clone(), BinOp::Divide, op2.clone()),
                        "iff" => (op.clone(), BinOp::Iff, op2.clone()),
                        "plus" => (op.clone(), BinOp::Plus, op2.clone()),
                        "mod" => (op.clone(), BinOp::ModOf, op2.clone()),
                        "mult" => (op.clone(), BinOp::Mult, op2.clone()),
                        "lt" => (op.clone(), BinOp::Lt, op2.clone()),
                        "or" => (op.clone(), BinOp::Or, op2.clone()),
                        "and" => (op.clone(), BinOp::And, op2.clone()),
                        _ => return None,
                    },
                    _ => return None,
                },
                _ => return None,
            },
            Term::Forall(Abstraction {
                body,
                var_ty,
                hint_name: _,
            }) => {
                let x = remove_unused_var(body.clone(), 0)?;
                (var_ty.clone(), BinOp::Imply, x)
            }
            _ => return None,
        })
    }
}
