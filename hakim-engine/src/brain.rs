use crate::parser::term_pretty_print;
use std::{fmt::Debug, iter::once, rc::Rc};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Axiom { ty: TermRef, unique_name: String },
    Universe { index: usize },
    Forall { var_ty: TermRef, body: TermRef },
    Var { index: usize },
    Number { value: i32 },
    App { func: TermRef, op: TermRef },
    Wild { index: usize },
}

pub type TermRef = Rc<Term>;

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut name_stack = vec![];
        f.write_str(&term_pretty_print(
            Rc::new(self.clone()),
            &mut name_stack,
            200,
        ))
    }
}

#[macro_export]
macro_rules! term_ref {
    {$input:expr} => (($input).clone());
    {$($i:tt)*} => (crate::TermRef::new(crate::term!($( $i)*)));
}

#[macro_export]
macro_rules! term {
    {forall $ty:expr , $($i:tt)*} => (crate::Term::Forall { var_ty: term_ref!($ty), body: (term_ref!($( $i)*)) });
    {axiom $name:expr , $($i:tt)*} => (crate::Term::Axiom { ty: term_ref!($( $i)*), unique_name: ($name).to_string() });
    {universe $input:expr} => (crate::Term::Universe { index: ($input) });
    {v $input:expr} => (crate::Term::Var { index: ($input) });
    {n $input:expr} => (crate::Term::Number { value: ($input) });
    {_ $input:expr} => (crate::Term::Wild { index: ($input) });
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

#[derive(Debug)]
pub enum Error {
    BadTerm,
    TypeMismatch(TermRef, TermRef),
    IsNotFunc,
}

pub fn match_term(t1: TermRef, t2: TermRef) -> Result<(), Error> {
    if t1 == t2 {
        Ok(())
    } else {
        Err(Error::TypeMismatch(t1, t2))
    }
}

pub fn create_infer_vec(n: usize) -> Vec<TermRef> {
    let mut r = vec![];
    for index in 0..n {
        r.push(TermRef::new(Term::Wild { index }))
    }
    r
}

pub fn match_and_infer(t1: TermRef, t2: TermRef, infers: &mut [TermRef]) -> Result<(), Error> {
    match (t1.as_ref(), t2.as_ref()) {
        (Term::Wild { index }, _) => {
            let i = *index;
            if infers[i] == t1 {
                infers[i] = t2.clone();
                Ok(())
            } else {
                match_and_infer(infers[i].clone(), t2, infers)
            }
        }
        (_, Term::Wild { index }) => {
            let i = *index;
            if infers[i] == t2 {
                infers[i] = t1.clone();
                Ok(())
            } else {
                match_and_infer(infers[i].clone(), t1, infers)
            }
        }
        (
            Term::App {
                func: func1,
                op: op1,
            },
            Term::App {
                func: func2,
                op: op2,
            },
        ) => {
            match_and_infer(func1.clone(), func2.clone(), infers)?;
            match_and_infer(op1.clone(), op2.clone(), infers)
        }
        (
            Term::Axiom {
                unique_name: u1, ..
            },
            Term::Axiom {
                unique_name: u2, ..
            },
        ) => {
            if u1 == u2 {
                Ok(())
            } else {
                Err(Error::TypeMismatch(t1, t2))
            }
        }
        _ => Err(Error::TypeMismatch(t1, t2)),
    }
}

pub fn subst<'a>(exp: TermRef, to_put: TermRef) -> TermRef {
    fn inner<'a>(exp: TermRef, to_put: TermRef, i: usize) -> TermRef {
        match exp.as_ref() {
            Term::Var { index } if *index == i => to_put,
            Term::Var { .. }
            | Term::Axiom { .. }
            | Term::Universe { .. }
            | Term::Number { .. }
            | Term::Wild { .. } => exp,
            Term::Forall { var_ty, body } => TermRef::new(Term::Forall {
                var_ty: inner(var_ty.clone(), to_put.clone(), i),
                body: inner(body.clone(), to_put, i + 1),
            }),
            Term::App { func, op } => TermRef::new(Term::App {
                func: inner(func.clone(), to_put.clone(), i),
                op: inner(op.clone(), to_put, i),
            }),
        }
    }
    inner(exp, to_put, 0)
}

pub fn increase_foreign_vars(term: TermRef, depth: usize) -> TermRef {
    match term.as_ref() {
        Term::Var { index } if *index >= depth => TermRef::new(Term::Var { index: index + 1 }),
        Term::Axiom { .. }
        | Term::Universe { .. }
        | Term::Number { .. }
        | Term::Var { .. }
        | Term::Wild { .. } => term,
        Term::Forall { var_ty, body } => {
            let var_ty = increase_foreign_vars(var_ty.clone(), depth);
            let body = increase_foreign_vars(body.clone(), depth + 1);
            TermRef::new(Term::Forall { var_ty, body })
        }
        Term::App { func, op } => {
            let func = increase_foreign_vars(func.clone(), depth);
            let op = increase_foreign_vars(op.clone(), depth);
            TermRef::new(Term::App { func, op })
        }
    }
}

fn type_of_inner(term: TermRef, var_ty_stack: &Vec<TermRef>) -> Result<TermRef, Error> {
    Ok(match term.as_ref() {
        Term::Axiom { ty, .. } => ty.clone(),
        Term::Universe { index } => TermRef::new(Term::Universe { index: index + 1 }),
        Term::Forall { var_ty, body } => {
            let vtt = type_of_inner(var_ty.clone(), var_ty_stack)?;
            let new_var_stack = var_ty_stack
                .iter()
                .chain(once(var_ty))
                .map(|x| increase_foreign_vars(x.clone(), 0))
                .collect();
            type_of_inner(body.clone(), &new_var_stack)?;
            vtt
        }
        Term::Var { index } => var_ty_stack
            .iter()
            .rev()
            .nth(*index)
            .ok_or(Error::BadTerm)?
            .clone(),
        Term::Number { .. } => term_ref!(axiom "ℤ".to_string(), universe 0),
        Term::App { func, op } => {
            let op_ty = type_of_inner(op.clone(), var_ty_stack)?;
            let func_type = type_of_inner(func.clone(), var_ty_stack)?;
            let (var_ty, body) = if let Term::Forall { var_ty, body } = func_type.as_ref() {
                (var_ty, body)
            } else {
                return Err(Error::IsNotFunc);
            };
            match_term(var_ty.clone(), op_ty)?;
            subst(body.clone(), op.clone())
        }
        Term::Wild { .. } => todo!(),
    })
}

pub fn type_of(term: TermRef) -> Result<TermRef, Error> {
    type_of_inner(term, &vec![])
}
