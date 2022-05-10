use crate::parser::term_pretty_print;
use std::{cmp::Ordering, fmt::Debug, hash::Hash, rc::Rc};

pub mod infer;
mod subtyping;

pub use subtyping::subtype_and_infer;

#[cfg(test)]
mod tests;

#[derive(Clone, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Abstraction {
    pub var_ty: TermRef,
    pub hint_name: Option<String>,
    pub body: TermRef,
}

// we implement this manually to ignore hint_name, so (forall a: T, a) is equal to (forall b: T, b)
impl PartialEq for Abstraction {
    fn eq(&self, other: &Self) -> bool {
        self.var_ty == other.var_ty && self.body == other.body
    }
}

// we implement this manually to ignore hint_name, so (forall a: T, a) is equal to (forall b: T, b)
impl Hash for Abstraction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.var_ty.hash(state);
        self.body.hash(state);
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Term {
    Axiom { ty: TermRef, unique_name: String },
    Universe { index: usize },
    Forall(Abstraction),
    Fun(Abstraction),
    Var { index: usize },
    Number { value: BigInt },
    App { func: TermRef, op: TermRef },
    Wild { index: usize, scope: usize },
}

pub type TermRef = Rc<Term>;

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&term_pretty_print(self, |_| true))
    }
}

#[macro_export]
macro_rules! term_ref {
    {$input:expr} => (($input).clone());
    {$($i:tt)*} => (crate::TermRef::new(crate::term!($( $i)*)));
}

#[macro_export]
macro_rules! term {
    {forall $ty:expr , $($i:tt)*} => (crate::Term::Forall(crate::Abstraction { var_ty: term_ref!($ty), hint_name: None, body: (term_ref!($( $i)*)) }));
    {fun $ty:expr , $($i:tt)*} => (crate::Term::Fun(crate::Abstraction { var_ty: term_ref!($ty), hint_name: None, body: (term_ref!($( $i)*)) }));
    {axiom $name:expr , $($i:tt)*} => (crate::Term::Axiom { ty: term_ref!($( $i)*), unique_name: ($name).to_string() });
    {universe $input:expr} => (crate::Term::Universe { index: ($input) });
    {v $input:expr} => (crate::Term::Var { index: ($input) });
    {n $input:expr} => (crate::Term::Number { value: ($input).into() });
    {_ $input:expr} => (crate::Term::Wild { index: ($input), scope: 0 });
    {$input:expr} => ($input);
}

#[macro_export]
macro_rules! app_ref {
    {$($i:tt)*} => (crate::TermRef::new(crate::app!($( $i)*)));
}

#[macro_export]
macro_rules! app {
    ( $x:expr , $y:expr ) => {
        crate::Term::App {
            func: ($x).clone(),
            op: ($y).clone(),
        }
    };
    ( $x:expr , $y:expr, $z:expr ) => {
        crate::Term::App {
            func: crate::TermRef::new(crate::Term::App {
                func: ($x).clone(),
                op: ($y).clone(),
            }),
            op: ($z).clone(),
        }
    };
    ( $x:expr , $y:expr, $z:expr, $w:expr ) => {
        crate::Term::App {
            func: crate::TermRef::new(crate::Term::App {
                func: TermRef::new(crate::Term::App {
                    func: ($x).clone(),
                    op: ($y).clone(),
                }),
                op: ($z).clone(),
            }),
            op: ($w).clone(),
        }
    };
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    ForiegnVariableInTerm(usize),
    TypeMismatch(TermRef, TermRef),
    IsNotFunc { value: TermRef, ty: TermRef },
    ContainsWild,
    IsNotUniverse,
    LoopOfInference(usize, TermRef),
    WildNeedLocalVar(usize),
}

pub type Result<T> = std::result::Result<T, Error>;

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use Error::*;

pub fn map_reduce_wild<T>(
    t: &Term,
    map: &mut impl FnMut(usize, usize) -> Option<T>,
    reduce: &impl Fn(T, T) -> T,
) -> Option<T> {
    let mut combine = |a, b| {
        let a = map_reduce_wild(a, map, reduce);
        let b = map_reduce_wild(b, map, reduce);
        match (a, b) {
            (Some(a), Some(b)) => Some(reduce(a, b)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
        }
    };
    match t {
        Term::Axiom { .. } | Term::Universe { .. } | Term::Var { .. } | Term::Number { .. } => None,
        Term::App { func, op } => combine(func, op),
        Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        })
        | Term::Fun(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) => combine(var_ty, body),
        Term::Wild { index, scope } => map(*index, *scope),
    }
}

pub fn for_each_wild(t: &Term, mut work: impl FnMut(usize, usize)) {
    map_reduce_wild(
        t,
        &mut |i, s| {
            work(i, s);
            Some(())
        },
        &|_, _| (),
    );
}

/// if expression contains some wilds, it will computes predict(i1) || predict(i2) || ... || predict(in)
/// when ik is id of wilds. In case of no wild, it will return false
pub fn predict_wild(t: &Term, predict: &impl Fn(usize, usize) -> bool) -> bool {
    map_reduce_wild(
        t,
        &mut |x, y| if predict(x, y) { Some(()) } else { None },
        &|_, _| (),
    )
    .is_some()
}

/// if expression contains some axiom, it will computes predict(i1) || predict(i2) || ... || predict(in)
/// when ik is unique_name of axioms. In case of no axiom, it will return false
pub fn map_reduce_axiom<T>(
    t: &Term,
    map: &mut impl FnMut(&str) -> Option<T>,
    reduce: &impl Fn(T, T) -> T,
) -> Option<T> {
    let mut combine = |a, b| {
        let a = map_reduce_axiom(a, map, reduce);
        let b = map_reduce_axiom(b, map, reduce);
        match (a, b) {
            (Some(a), Some(b)) => Some(reduce(a, b)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
        }
    };
    match t {
        Term::Wild { .. } | Term::Universe { .. } | Term::Var { .. } | Term::Number { .. } => None,
        Term::App { func, op } => combine(func, op),
        Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        })
        | Term::Fun(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) => combine(var_ty, body),
        Term::Axiom { unique_name, .. } => map(unique_name),
    }
}

/// if expression contains some axiom, it will computes predict(i1) || predict(i2) || ... || predict(in)
/// when ik is unique_name of axioms. In case of no axiom, it will return false
pub fn predict_axiom(t: &Term, predict: impl Fn(&str) -> bool) -> bool {
    map_reduce_axiom(
        t,
        &mut |x| if predict(x) { Some(()) } else { None },
        &|_, _| (),
    )
    .is_some()
}

pub fn contains_wild(t: &Term) -> bool {
    predict_wild(t, &|_, _| true)
}

pub fn remove_unused_var(t: TermRef, depth: usize) -> Option<TermRef> {
    fn for_abs(
        Abstraction {
            var_ty,
            body,
            hint_name,
        }: &Abstraction,
        depth: usize,
    ) -> Option<Abstraction> {
        let var_ty = remove_unused_var(var_ty.clone(), depth)?;
        let body = remove_unused_var(body.clone(), depth + 1)?;
        let hint_name = hint_name.clone();
        Some(Abstraction {
            var_ty,
            body,
            hint_name,
        })
    }
    Some(match t.as_ref() {
        Term::Axiom { .. } | Term::Universe { .. } | Term::Wild { .. } | Term::Number { .. } => t,
        Term::App { func, op } => {
            let func = remove_unused_var(func.clone(), depth)?;
            let op = remove_unused_var(op.clone(), depth)?;
            app_ref!(func, op)
        }
        Term::Forall(x) => TermRef::new(Term::Forall(for_abs(x, depth)?)),
        Term::Fun(x) => TermRef::new(Term::Fun(for_abs(x, depth)?)),
        Term::Var { index } => {
            let i = *index;
            match i.cmp(&depth) {
                Ordering::Less => term_ref!(v i),
                Ordering::Equal => return None,
                Ordering::Greater => term_ref!(v i - 1),
            }
        }
    })
}

fn deny_wild(t: &Term) -> Result<()> {
    if contains_wild(t) {
        Err(ContainsWild)
    } else {
        Ok(())
    }
}

pub fn fill_wild_with_depth(
    t: TermRef,
    f: &impl Fn(usize, usize, usize) -> TermRef,
    depth: usize,
) -> TermRef {
    fn for_abs(
        Abstraction {
            body,
            var_ty,
            hint_name,
        }: &Abstraction,
        f: &impl Fn(usize, usize, usize) -> TermRef,
        depth: usize,
    ) -> Abstraction {
        let body = fill_wild_with_depth(body.clone(), f, depth + 1);
        let var_ty = fill_wild_with_depth(var_ty.clone(), f, depth);
        let hint_name = hint_name.clone();
        Abstraction {
            var_ty,
            hint_name,
            body,
        }
    }
    match t.as_ref() {
        Term::Axiom { .. } | Term::Universe { .. } | Term::Var { .. } | Term::Number { .. } => t,
        Term::App { func, op } => app_ref!(
            fill_wild_with_depth(func.clone(), f, depth),
            fill_wild_with_depth(op.clone(), f, depth)
        ),
        Term::Forall(abs) => TermRef::new(Term::Forall(for_abs(abs, f, depth))),
        Term::Fun(abs) => TermRef::new(Term::Fun(for_abs(abs, f, depth))),
        Term::Wild { index, scope } => f(*index, *scope, depth),
    }
}

pub fn fill_wild(t: TermRef, f: &impl Fn(usize, usize) -> TermRef) -> TermRef {
    fill_wild_with_depth(t, &|a, b, _| f(a, b), 0)
}

pub fn normalize(t: TermRef) -> TermRef {
    fn for_abs(a: Abstraction) -> Abstraction {
        Abstraction {
            var_ty: normalize(a.var_ty),
            body: normalize(a.body),
            hint_name: a.hint_name,
        }
    }
    match t.as_ref() {
        Term::Var { .. }
        | Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Number { .. }
        | Term::Wild { .. } => t,
        Term::Forall(x) => TermRef::new(Term::Forall(for_abs(x.clone()))),
        Term::Fun(x) => {
            if let Term::App { func, op } = x.body.as_ref() {
                if **op == (Term::Var { index: 0 }) {
                    if let Some(x) = remove_unused_var(func.clone(), 0) {
                        return normalize(x);
                    }
                }
            }
            TermRef::new(Term::Fun(for_abs(x.clone())))
        }
        Term::App { func, op } => {
            let func = normalize(func.clone());
            if let Term::Fun(x) = func.as_ref() {
                return normalize(subst(x.body.clone(), op.clone()));
            }
            let op = normalize(op.clone());
            app_ref!(func, op)
        }
    }
}

pub fn subst(exp: TermRef, to_put: TermRef) -> TermRef {
    fn for_abs(abs: Abstraction, to_put: TermRef, i: usize) -> Abstraction {
        let var_ty = inner(abs.var_ty, to_put.clone(), i);
        let to_put = increase_foreign_vars(to_put, 0);
        let body = inner(abs.body, to_put, i + 1);
        Abstraction {
            var_ty,
            body,
            hint_name: abs.hint_name,
        }
    }
    fn inner(exp: TermRef, to_put: TermRef, i: usize) -> TermRef {
        match exp.as_ref() {
            Term::Var { index } => match i.cmp(index) {
                Ordering::Less => term_ref!(v index - 1),
                Ordering::Equal => to_put,
                Ordering::Greater => {
                    let x = *index;
                    term_ref!(v x)
                }
            },
            Term::Axiom { .. }
            | Term::Universe { .. }
            | Term::Number { .. }
            | Term::Wild { .. } => exp,
            Term::Forall(a) => TermRef::new(Term::Forall(for_abs(a.clone(), to_put, i))),
            Term::Fun(a) => TermRef::new(Term::Fun(for_abs(a.clone(), to_put, i))),
            Term::App { func, op } => TermRef::new(Term::App {
                func: inner(func.clone(), to_put.clone(), i),
                op: inner(op.clone(), to_put, i),
            }),
        }
    }
    inner(exp, to_put, 0)
}

pub fn increase_foreign_vars(term: TermRef, depth: usize) -> TermRef {
    fn for_abs(
        Abstraction {
            var_ty,
            body,
            hint_name,
        }: &Abstraction,
        depth: usize,
    ) -> Abstraction {
        let var_ty = increase_foreign_vars(var_ty.clone(), depth);
        let body = increase_foreign_vars(body.clone(), depth + 1);
        let hint_name = hint_name.clone();
        Abstraction {
            var_ty,
            body,
            hint_name,
        }
    }
    match term.as_ref() {
        Term::Var { index } if *index >= depth => TermRef::new(Term::Var { index: index + 1 }),
        Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Number { .. }
        | Term::Var { .. }
        | Term::Wild { .. } => term,
        Term::Forall(a) => TermRef::new(Term::Forall(for_abs(a, depth))),
        Term::Fun(a) => TermRef::new(Term::Fun(for_abs(a, depth))),
        Term::App { func, op } => {
            let func = increase_foreign_vars(func.clone(), depth);
            let op = increase_foreign_vars(op.clone(), depth);
            TermRef::new(Term::App { func, op })
        }
    }
}

pub fn type_of(term: TermRef) -> Result<TermRef> {
    deny_wild(&term)?;
    infer::type_of_inner(term, &[], &mut infer::InferResults::new(0))
}

pub fn get_forall_depth(term: &Term) -> usize {
    match term {
        Term::Forall(Abstraction { body, .. }) => get_forall_depth(body) + 1,
        _ => 0,
    }
}
