macro_rules! binop {
    ($($name:ident, $prec:literal, $assoc:ident, $txt:literal);*;) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub enum BinOp {
            $(
                $name,
            )*
        }

        impl Display for BinOp {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
                f.write_str(match self {
                    $(
                        $name => $txt,
                    )*
                })
            }
        }

        impl BinOp {
            pub fn from_str(op: &str) -> Option<Self> {
                Some(match op {
                    $(
                        $txt => $name,
                    )*
                    _ => return None,
                })
            }

            pub fn prec(&self) -> PrecLevel {
                PrecLevel(match self {
                    $(
                        $name => $prec,
                    )*
                })
            }

            pub fn assoc(&self) -> Assoc {
                match self {
                    $(
                        $name => $assoc,
                    )*
                }
            }
        }
    };
}

// Source of prec and assoc: https://coq.inria.fr/library/Coq.Init.Notations.html
binop! {
    And, 79, Right, "∧";
    App, 1, Left, " ";
    Divide, 70, No, "|";
    Eq, 70, No, "=";
    Ge, 70, No, "≥";
    Gt, 70, No, ">";
    Iff, 99, No, "↔";
    Imply, 98, Right, "→";
    Included, 70, No, "⊆";
    Intersection, 40, Left, "∩";
    Inset, 70, No, "∈";
    Le, 70, No, "≤";
    Lt, 70, No, "<";
    Minus, 50, Left, "-";
    ModOf, 60, Left, "mod";
    Mult, 40, Left, "*";
    Or, 85, Right, "∨";
    Plus, 50, Left, "+";
    Pow, 30, Right, "^";
    Union, 50, Left, "∪";
    Setminus, 30, Left, "∖";
}

#[derive(PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
    No,
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

use super::{InferGenerator, PrecLevel};

impl BinOp {
    pub fn level_left(&self) -> PrecLevel {
        match self.assoc() {
            Left => self.prec(),
            No | Right => self.prec() - 1,
        }
    }

    pub fn level_right(&self) -> PrecLevel {
        match self.assoc() {
            Right => self.prec(),
            No | Left => self.prec() - 1,
        }
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
            Ge => Le.run_on_term(infer_cnt, r, l),
            Gt => app_ref!(lt(), r, l),
            Iff => app_ref!(
                and(),
                term_ref!(forall l, increase_foreign_vars(r.clone(), 0)),
                term_ref!(forall r, increase_foreign_vars(l, 0))
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
            Le => app_ref!(or(), app_ref!(lt(), l, r), app_ref!(eq(), z(), l, r)),
            Lt => app_ref!(lt(), l, r),
            Minus => app_ref!(minus(), l, r),
            ModOf => app_ref!(mod_of(), l, r),
            Mult => app_ref!(mult(), l, r),
            Or => app_ref!(or(), l, r),
            Plus => app_ref!(plus(), l, r),
            Pow => app_ref!(pow(), l, r),
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
            Term::App {
                func: original_func,
                op: op2,
            } => match original_func.as_ref() {
                Term::App { func, op } => match func.as_ref() {
                    Term::App { func, op: _ } => match func.as_ref() {
                        Term::Axiom { ty: _, unique_name } => match unique_name.as_str() {
                            "eq" => (op.clone(), BinOp::Eq, op2.clone()),
                            "inset" => (op.clone(), BinOp::Inset, op2.clone()),
                            "included" => (op.clone(), BinOp::Included, op2.clone()),
                            "intersection" => (op.clone(), BinOp::Intersection, op2.clone()),
                            "union" => (op.clone(), BinOp::Union, op2.clone()),
                            "setminus" => (op.clone(), BinOp::Setminus, op2.clone()),
                            _ => (original_func.clone(), BinOp::App, op2.clone()),
                        },
                        _ => (original_func.clone(), BinOp::App, op2.clone()),
                    },
                    Term::Axiom { ty: _, unique_name } => match unique_name.as_str() {
                        "divide" => (op.clone(), BinOp::Divide, op2.clone()),
                        "iff" => (op.clone(), BinOp::Iff, op2.clone()),
                        "plus" => (op.clone(), BinOp::Plus, op2.clone()),
                        "pow" => (op.clone(), BinOp::Pow, op2.clone()),
                        "minus" => (op.clone(), BinOp::Minus, op2.clone()),
                        "mod_of" => (op.clone(), BinOp::ModOf, op2.clone()),
                        "mult" => (op.clone(), BinOp::Mult, op2.clone()),
                        "lt" => (op.clone(), BinOp::Lt, op2.clone()),
                        #[allow(clippy::never_loop)]
                        "or" => loop {
                            if let Some((a1, BinOp::Lt, b1)) = BinOp::detect(op) {
                                if let Some((a2, BinOp::Eq, b2)) = BinOp::detect(op2) {
                                    if a1 == a2 && b1 == b2 {
                                        break (a1, BinOp::Le, b1);
                                    }
                                }
                            }
                            break (op.clone(), BinOp::Or, op2.clone());
                        },
                        #[allow(clippy::never_loop)]
                        "and" => loop {
                            if let Some((a1, BinOp::Imply, b1)) = BinOp::detect(op) {
                                if let Some((b2, BinOp::Imply, a2)) = BinOp::detect(op2) {
                                    if a1 == a2 && b1 == b2 {
                                        break (a1, BinOp::Iff, b1);
                                    }
                                }
                            }
                            break (op.clone(), BinOp::And, op2.clone());
                        },
                        _ => (original_func.clone(), BinOp::App, op2.clone()),
                    },
                    _ => (original_func.clone(), BinOp::App, op2.clone()),
                },
                _ => (original_func.clone(), BinOp::App, op2.clone()),
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
