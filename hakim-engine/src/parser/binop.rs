macro_rules! binop {
    ($($name:ident, $prec:literal, $assoc:ident, $txt:literal);*;) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
        pub enum BinOp {
            $(
                $name,
            )*
        }

        pub(super) const ALL_BINOPS: &[BinOp] = &[$($name,)*];

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
    And, 80, Right, "∧";
    App, 1, Left, " ";
    Cons, 45, Right, "::";
    Divide, 70, No, "|";
    Eq, 70, No, "=";
    Ge, 70, No, "≥";
    Gt, 70, No, ">";
    Iff, 95, No, "↔";
    Imply, 99, Right, "→";
    Included, 70, No, "⊆";
    Inlist, 70, No, "in";
    Intersection, 40, Left, "∩";
    Inset, 70, No, "∈";
    Le, 70, No, "≤";
    Lt, 70, No, "<";
    Minus, 50, Left, "-";
    ModOf, 60, Left, "mod";
    Mult, 40, Left, "*";
    Or, 85, Right, "∨";
    Plus, 50, Left, "+";
    PlusList, 50, Left, "++";
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

use std::{
    collections::HashSet,
    fmt::{Display, Formatter},
};

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
        self.run_on_term_with_ty(l, r, || {
            let i = infer_cnt.generate();
            term_ref!(_ i)
        })
    }

    pub fn run_on_term_with_ty(
        &self,
        l: TermRef,
        r: TermRef,
        ty: impl FnOnce() -> TermRef,
    ) -> TermRef {
        match self {
            And => app_ref!(and(), l, r),
            App => app_ref!(l, r),
            Cons => app_ref!(cons(), ty(), l, r),
            Divide => app_ref!(divide(), l, r),
            Eq => {
                app_ref!(eq(), ty(), l, r)
            }
            Ge => Le.run_on_term_with_ty(r, l, ty),
            Gt => app_ref!(lt(), r, l),
            Iff => app_ref!(
                and(),
                term_ref!(forall l, increase_foreign_vars(r.clone())),
                term_ref!(forall r, increase_foreign_vars(l))
            ),
            Imply => term_ref!(forall l, increase_foreign_vars(r)),
            Included => {
                app_ref!(included(), ty(), l, r)
            }
            Inlist => {
                app_ref!(inlist(), ty(), l, r)
            }
            Intersection => {
                app_ref!(intersection(), ty(), l, r)
            }
            Inset => {
                app_ref!(inset(), ty(), l, r)
            }
            Le => app_ref!(or(), app_ref!(lt(), l, r), app_ref!(eq(), z(), l, r)),
            Lt => app_ref!(lt(), l, r),
            Minus => app_ref!(minus(), l, r),
            ModOf => app_ref!(mod_of(), l, r),
            Mult => app_ref!(mult(), l, r),
            Or => app_ref!(or(), l, r),
            Plus => app_ref!(plus(), ty(), l, r),
            PlusList => {
                app_ref!(plus_list(), ty(), l, r)
            }
            Pow => app_ref!(pow(), l, r),
            Union => {
                app_ref!(union(), ty(), l, r)
            }
            Setminus => {
                app_ref!(setminus(), ty(), l, r)
            }
        }
    }

    pub fn detect(t: &Term) -> Option<(TermRef, Self, TermRef)> {
        let (a, b, c, _) = Self::detect_custom(t, &HashSet::from([]))?;
        Some((a, b, c))
    }

    pub fn detect_custom(
        t: &Term,
        disabled: &HashSet<Self>,
    ) -> Option<(TermRef, Self, TermRef, Option<TermRef>)> {
        macro_rules! found {
            ($a:expr , $op:ident , $b:expr) => {
                if !disabled.contains(&BinOp::$op) {
                    return Some((($a).clone(), BinOp::$op, ($b).clone(), None));
                }
            };
            ($a:expr , $op:ident , $b:expr, $c:expr) => {
                if !disabled.contains(&BinOp::$op) {
                    return Some((($a).clone(), BinOp::$op, ($b).clone(), Some(($c).clone())));
                }
            };
        }
        match t {
            Term::App {
                func: original_func,
                op: op2,
            } => match original_func.as_ref() {
                Term::App { func, op } => match func.as_ref() {
                    Term::App { func, op: ty } => match func.as_ref() {
                        Term::Axiom { ty: _, unique_name } => match unique_name.as_str() {
                            "cons" => found!(op, Cons, op2, ty),
                            "eq" => found!(op, Eq, op2, ty),
                            "plus" => found!(op, Plus, op2, ty),
                            "included" => found!(op, Included, op2, ty),
                            "inlist" => found!(op, Inlist, op2, ty),
                            "inset" => found!(op, Inset, op2, ty),
                            "intersection" => found!(op, Intersection, op2, ty),
                            "union" => found!(op, Union, op2, ty),
                            "setminus" => found!(op, Setminus, op2, ty),
                            "plus_list" => found!(op, PlusList, op2, ty),
                            _ => found!(original_func, App, op2, ty),
                        },
                        _ => found!(original_func, App, op2),
                    },
                    Term::Axiom { ty: _, unique_name } => match unique_name.as_str() {
                        "divide" => found!(op, Divide, op2),
                        "iff" => found!(op, Iff, op2),
                        "pow" => found!(op, Pow, op2),
                        "minus" => found!(op, Minus, op2),
                        "mod_of" => found!(op, ModOf, op2),
                        "mult" => found!(op, Mult, op2),
                        "lt" => found!(op, Lt, op2),
                        "or" => {
                            if let Some((a1, BinOp::Lt, b1)) = BinOp::detect(op) {
                                if let Some((a2, BinOp::Eq, b2)) = BinOp::detect(op2) {
                                    if a1 == a2 && b1 == b2 {
                                        found!(a1, Le, b1);
                                    }
                                }
                            }
                            found!(op, Or, op2);
                        }
                        "and" => {
                            if let Some((a1, BinOp::Imply, b1)) = BinOp::detect(op) {
                                if let Some((b2, BinOp::Imply, a2)) = BinOp::detect(op2) {
                                    if a1 == a2 && b1 == b2 {
                                        found!(a1, Iff, b1);
                                    }
                                }
                            }
                            found!(op, And, op2);
                        }
                        _ => found!(original_func, App, op2),
                    },
                    _ => found!(original_func, App, op2),
                },
                _ => found!(original_func, App, op2),
            },
            Term::Forall(Abstraction {
                body,
                var_ty,
                hint_name: _,
            }) => {
                let x = remove_unused_var(body.clone())?;
                found!(var_ty, Imply, x);
            }
            _ => (),
        }
        None
    }
}
