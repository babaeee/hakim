use crate::parser::{term_pretty_print, PrettyPrintConfig};
use std::{cmp::Ordering, fmt::Debug, hash::Hash, rc::Rc};

pub mod detect;
pub mod infer;
mod subtyping;

pub use subtyping::subtype_and_infer;

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Eq, PartialOrd, Ord, Serialize, Deserialize)]
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
    Axiom {
        ty: TermRef,
        unique_name: String,
    },
    Universe {
        index: usize,
    },
    Forall(Abstraction),
    Fun(Abstraction),
    Var {
        index: usize,
    },
    Number {
        value: BigInt,
    },
    /// Stores real numbers. 10.234 will be stored as `NumberR { value: 10234, point: 3 }`
    NumberR {
        value: BigInt,
        point: usize,
    },
    App {
        func: TermRef,
        op: TermRef,
    },
    Wild {
        index: usize,
        scope: Option<Vec<usize>>,
    },
}

pub type TermRef = Rc<Term>;

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&term_pretty_print::<String, _>(
            self,
            |_| true,
            &PrettyPrintConfig::default(),
        ))
    }
}

#[macro_export]
macro_rules! term_ref {
    {$input:expr} => (($input).clone());
    {$($i:tt)*} => ($crate::TermRef::new($crate::term!($( $i)*)));
}

#[macro_export]
macro_rules! term {
    {forall $ty:expr , $($i:tt)*} => ($crate::Term::Forall($crate::Abstraction { var_ty: term_ref!($ty), hint_name: None, body: (term_ref!($( $i)*)) }));
    {fun $ty:expr , $($i:tt)*} => ($crate::Term::Fun($crate::Abstraction { var_ty: term_ref!($ty), hint_name: None, body: (term_ref!($( $i)*)) }));
    {axiom $name:expr , $($i:tt)*} => ($crate::Term::Axiom { ty: term_ref!($( $i)*), unique_name: ($name).to_string() });
    {universe $input:expr} => ($crate::Term::Universe { index: ($input) });
    {v $input:expr} => ($crate::Term::Var { index: ($input) });
    {n $input:expr} => ($crate::Term::Number { value: ($input).into() });
    {_ $input:expr} => ($crate::Term::Wild { index: ($input), scope: None });
    {$input:expr} => ($input);
}

#[macro_export]
macro_rules! app_ref {
    {$($i:tt)*} => ($crate::TermRef::new($crate::app!($( $i)*)));
}

#[macro_export]
macro_rules! app {
    ( $x:expr , $y:expr ) => {
        $crate::Term::App {
            func: ($x).clone(),
            op: ($y).clone(),
        }
    };
    ( $x:expr , $y:expr, $z:expr ) => {
        $crate::Term::App {
            func: $crate::TermRef::new($crate::Term::App {
                func: ($x).clone(),
                op: ($y).clone(),
            }),
            op: ($z).clone(),
        }
    };
    ( $x:expr , $y:expr, $z:expr, $w:expr ) => {
        $crate::Term::App {
            func: $crate::TermRef::new($crate::Term::App {
                func: TermRef::new($crate::Term::App {
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
pub enum ErrorReason {
    ForiegnVariableInTerm(usize),
    TypeMismatch(TermRef, TermRef),
    IsNotFunc { value: TermRef, ty: TermRef },
    ContainsWild,
    IsNotUniverse,
    LoopOfInference(usize, TermRef),
    WildNeedLocalVar(usize),
}

#[derive(Debug, PartialEq, Eq)]
pub enum ErrorContext {
    InMatching(TermRef, TermRef),
    InTypechecking(TermRef),
}

#[derive(PartialEq, Eq)]
pub struct Error {
    reason: ErrorReason,
    context: Vec<ErrorContext>,
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "$error:\n    {:?}\n$in_context:\n", self.reason)?;
        for x in &self.context {
            writeln!(f, "    {x:?}")?;
        }
        Ok(())
    }
}

impl From<ErrorReason> for Error {
    fn from(reason: ErrorReason) -> Self {
        Error {
            reason,
            context: vec![],
        }
    }
}

impl Error {
    fn with_context(mut self, context: ErrorContext) -> Self {
        self.context.push(context);
        self
    }
}

pub type Result<T> = std::result::Result<T, Error>;

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use ErrorReason::*;

pub fn map_reduce_wild<T>(
    t: &Term,
    map: &mut impl FnMut(usize, Option<&[usize]>) -> Option<T>,
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
        Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Var { .. }
        | Term::Number { .. }
        | Term::NumberR { .. } => None,
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
        Term::Wild { index, scope } => map(*index, scope.as_deref()),
    }
}

pub fn for_each_wild(t: &Term, mut work: impl FnMut(usize, Option<&[usize]>)) {
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
pub fn predict_wild(t: &Term, predict: &impl Fn(usize, Option<&[usize]>) -> bool) -> bool {
    map_reduce_wild(
        t,
        &mut |x, y| if predict(x, y) { Some(()) } else { None },
        &|_, _| (),
    )
    .is_some()
}

pub fn fill_axiom(t: TermRef, converter: impl Fn(&str, TermRef, usize) -> TermRef) -> TermRef {
    fn for_abs(
        abs: &Abstraction,
        f: &impl Fn(&str, TermRef, usize) -> TermRef,
        depth: usize,
    ) -> Abstraction {
        let abs = abs.clone();
        Abstraction {
            var_ty: fa_rec(abs.var_ty, f, depth),
            hint_name: abs.hint_name,
            body: fa_rec(abs.body, f, depth + 1),
        }
    }
    fn fa_rec(t: TermRef, f: &impl Fn(&str, TermRef, usize) -> TermRef, depth: usize) -> TermRef {
        match t.as_ref() {
            Term::Axiom { ty, unique_name } => f(unique_name, ty.clone(), depth),
            Term::Wild { .. }
            | Term::NumberR { .. }
            | Term::Number { .. }
            | Term::Var { .. }
            | Term::Universe { .. } => t,
            Term::Forall(abs) => TermRef::new(Term::Forall(for_abs(abs, f, depth))),
            Term::Fun(abs) => TermRef::new(Term::Fun(for_abs(abs, f, depth))),
            Term::App { func, op } => {
                app_ref!(fa_rec(func.clone(), f, depth), fa_rec(op.clone(), f, depth))
            }
        }
    }
    fa_rec(t, &converter, 0)
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
        Term::Wild { .. }
        | Term::Universe { .. }
        | Term::Var { .. }
        | Term::Number { .. }
        | Term::NumberR { .. } => None,
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

pub fn remove_unused_var(t: TermRef) -> Option<TermRef> {
    let mut is_unused = true;
    let t = map_foreign_vars(t, |x, _| {
        if x == 0 {
            is_unused = false;
            0
        } else {
            x - 1
        }
    });
    is_unused.then_some(t)
}

fn deny_wild(t: &Term) -> Result<()> {
    if contains_wild(t) {
        Err(ContainsWild.into())
    } else {
        Ok(())
    }
}

pub fn fill_wild_with_depth(
    t: TermRef,
    f: &mut impl FnMut(usize, Option<&[usize]>, usize) -> TermRef,
    depth: usize,
) -> TermRef {
    fn for_abs(
        Abstraction {
            body,
            var_ty,
            hint_name,
        }: &Abstraction,
        f: &mut impl FnMut(usize, Option<&[usize]>, usize) -> TermRef,
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
        Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Var { .. }
        | Term::Number { .. }
        | Term::NumberR { .. } => t,
        Term::App { func, op } => app_ref!(
            fill_wild_with_depth(func.clone(), f, depth),
            fill_wild_with_depth(op.clone(), f, depth)
        ),
        Term::Forall(abs) => TermRef::new(Term::Forall(for_abs(abs, f, depth))),
        Term::Fun(abs) => TermRef::new(Term::Fun(for_abs(abs, f, depth))),
        Term::Wild { index, scope } => f(*index, scope.as_deref(), depth),
    }
}

pub fn fill_wild(
    t: TermRef,
    f: &impl Fn(usize, Option<&[usize]>) -> Result<TermRef>,
) -> Result<TermRef> {
    let mut err = None;
    let r = fill_wild_with_depth(
        t,
        &mut |a, b, _| match f(a, b) {
            Ok(x) => x,
            Err(e) => {
                err = Some(e);
                term_ref!(universe 0)
            }
        },
        0,
    );
    match err {
        Some(e) => Err(e),
        None => Ok(r),
    }
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
        | Term::NumberR { .. }
        | Term::Wild { .. } => t,
        Term::Forall(x) => TermRef::new(Term::Forall(for_abs(x.clone()))),
        Term::Fun(x) => {
            if let Term::App { func, op } = x.body.as_ref() {
                if **op == (Term::Var { index: 0 }) {
                    if let Some(x) = remove_unused_var(func.clone()) {
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
        let to_put = increase_foreign_vars(to_put);
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
            Term::Wild {
                index,
                scope: Some(v),
            } => TermRef::new(Term::Wild {
                index: *index,
                scope: Some(
                    v.iter()
                        .map(|&index| match i.cmp(&index) {
                            Ordering::Less => index - 1,
                            // TODO: this is not implemented correctly
                            Ordering::Equal => 300000,
                            Ordering::Greater => index,
                        })
                        .collect(),
                ),
            }),
            Term::Axiom { .. }
            | Term::Universe { .. }
            | Term::Number { .. }
            | Term::NumberR { .. }
            | Term::Wild { scope: None, .. } => exp,
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

pub fn increase_foreign_vars(term: TermRef) -> TermRef {
    map_foreign_vars(term, |x, _| x + 1)
}

pub fn map_foreign_vars(term: TermRef, mut f: impl FnMut(usize, bool) -> usize) -> TermRef {
    pub fn map_foreign_vars_inner(
        term: TermRef,
        depth: usize,
        f: &mut impl FnMut(usize, bool) -> usize,
    ) -> TermRef {
        fn for_abs(
            Abstraction {
                var_ty,
                body,
                hint_name,
            }: &Abstraction,
            depth: usize,
            f: &mut impl FnMut(usize, bool) -> usize,
        ) -> Abstraction {
            let var_ty = map_foreign_vars_inner(var_ty.clone(), depth, f);
            let body = map_foreign_vars_inner(body.clone(), depth + 1, f);
            let hint_name = hint_name.clone();
            Abstraction {
                var_ty,
                body,
                hint_name,
            }
        }
        match term.as_ref() {
            Term::Var { index } if *index >= depth => TermRef::new(Term::Var {
                index: f(*index - depth, true) + depth,
            }),
            Term::Wild {
                index,
                scope: Some(v),
            } => {
                let next_scope = v
                    .iter()
                    .map(|&x| {
                        if x >= depth {
                            f(x - depth, false) + depth
                        } else {
                            x
                        }
                    })
                    .collect();
                TermRef::new(Term::Wild {
                    index: *index,
                    scope: Some(next_scope),
                })
            }
            Term::Wild { scope: None, .. }
            | Term::Axiom { .. }
            | Term::Universe { .. }
            | Term::Number { .. }
            | Term::NumberR { .. }
            | Term::Var { .. } => term,
            Term::Forall(a) => TermRef::new(Term::Forall(for_abs(a, depth, f))),
            Term::Fun(a) => TermRef::new(Term::Fun(for_abs(a, depth, f))),
            Term::App { func, op } => {
                let func = map_foreign_vars_inner(func.clone(), depth, f);
                let op = map_foreign_vars_inner(op.clone(), depth, f);
                TermRef::new(Term::App { func, op })
            }
        }
    }
    map_foreign_vars_inner(term, 0, &mut f)
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

pub fn good_char(c: char) -> bool {
    c.is_ascii_graphic() || c == ' '
}

pub fn definitely_inequal(t1: &Term, t2: &Term) -> bool {
    use detect::detect_char;
    if let Some(c1) = detect_char(t1) {
        if let Some(c2) = detect_char(t2) {
            return c1 != c2;
        }
    }
    false
}
