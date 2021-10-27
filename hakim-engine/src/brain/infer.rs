use super::{fill_wild, increase_foreign_vars, normalize, subst, Error::*, Result, Term, TermRef};
use crate::Abstraction;
use crate::{brain::get_universe, term_ref};

use std::cmp::max;
use std::iter::once;

pub struct InferResults {
    pub n: usize,
    pub terms: Vec<TermRef>,
    pub tys: Vec<TermRef>,
}

impl InferResults {
    pub fn new(n: usize) -> InferResults {
        let mut terms = vec![];
        let mut tys = vec![];
        for index in 0..n {
            terms.push(TermRef::new(Term::Wild { index }))
        }
        for index in n..2 * n {
            tys.push(TermRef::new(Term::Wild { index }))
        }
        InferResults { terms, tys, n }
    }
    fn get(&self, i: usize) -> TermRef {
        if i < self.n {
            self.terms[i].clone()
        } else {
            self.tys[i - self.n].clone()
        }
    }
    fn set(&mut self, i: usize, term: TermRef) {
        if i < self.n {
            self.terms[i] = term;
        } else {
            self.tys[i - self.n] = term;
        }
        self.relax();
    }
    fn type_of(&self, i: usize) -> TermRef {
        if i < self.n {
            self.tys[i].clone()
        } else {
            todo!();
        }
    }
    fn relax(&mut self) {
        self.terms = self
            .terms
            .iter()
            .map(|x| fill_wild(x.clone(), &|i| self.get(i)))
            .collect();
        self.tys = self
            .tys
            .iter()
            .map(|x| fill_wild(x.clone(), &|i| self.get(i)))
            .collect();
    }
}

fn match_and_infer_without_normalize(
    t1: TermRef,
    t2: TermRef,
    infers: &mut InferResults,
) -> Result<()> {
    fn for_abs(a1: Abstraction, a2: Abstraction, infers: &mut InferResults) -> Result<()> {
        match_and_infer_without_normalize(a1.var_ty, a2.var_ty, infers)?;
        match_and_infer_without_normalize(a1.body, a2.body, infers)
    }
    match (t1.as_ref(), t2.as_ref()) {
        (Term::Wild { index }, _) => {
            let i = *index;
            if infers.get(i) == t1 {
                infers.set(i, t2.clone());
                Ok(())
            } else {
                match_and_infer_without_normalize(infers.get(i), t2, infers)
            }
        }
        (_, Term::Wild { index }) => {
            let i = *index;
            if infers.get(i) == t2 {
                infers.set(i, t1.clone());
                Ok(())
            } else {
                match_and_infer_without_normalize(infers.get(i), t1, infers)
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
            match_and_infer_without_normalize(func1.clone(), func2.clone(), infers)?;
            match_and_infer_without_normalize(op1.clone(), op2.clone(), infers)
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
                Err(TypeMismatch(t1, t2))
            }
        }
        (Term::Universe { index: i1 }, Term::Universe { index: i2 }) => {
            if i1 == i2 {
                Ok(())
            } else {
                Err(TypeMismatch(t1, t2))
            }
        }
        (Term::Number { value: i1 }, Term::Number { value: i2 }) => {
            if i1 == i2 {
                Ok(())
            } else {
                Err(TypeMismatch(t1, t2))
            }
        }
        (Term::Forall(a1), Term::Forall(a2)) | (Term::Fun(a1), Term::Fun(a2)) => {
            for_abs(a1.clone(), a2.clone(), infers)
        }
        (Term::Var { index: i1 }, Term::Var { index: i2 }) => {
            if i1 == i2 {
                Ok(())
            } else {
                Err(TypeMismatch(t1, t2))
            }
        }
        _ => Err(TypeMismatch(t1, t2)),
    }
}

pub fn match_and_infer(t1: TermRef, t2: TermRef, infers: &mut InferResults) -> Result<()> {
    let t1 = normalize(t1);
    let t2 = normalize(t2);
    match_and_infer_without_normalize(t1, t2, infers)
}

pub fn type_of_inner(
    term: TermRef,
    var_ty_stack: &[TermRef],
    infers: &mut InferResults,
) -> Result<TermRef> {
    Ok(match term.as_ref() {
        Term::Axiom { ty, .. } => ty.clone(),
        Term::Universe { index } => TermRef::new(Term::Universe { index: index + 1 }),
        Term::Forall(Abstraction { var_ty, body }) => {
            let vtt = get_universe(type_of_inner(var_ty.clone(), var_ty_stack, infers)?)?;
            let new_var_stack = var_ty_stack
                .iter()
                .chain(once(var_ty))
                .map(|x| increase_foreign_vars(x.clone(), 0))
                .collect::<Vec<_>>();
            let body_ty = get_universe(type_of_inner(body.clone(), &new_var_stack, infers)?)?;
            term_ref!(universe max(vtt, body_ty))
        }
        Term::Fun(Abstraction { var_ty, body }) => {
            get_universe(type_of_inner(var_ty.clone(), var_ty_stack, infers)?)?;
            let new_var_stack = var_ty_stack
                .iter()
                .chain(once(var_ty))
                .map(|x| increase_foreign_vars(x.clone(), 0))
                .collect::<Vec<_>>();
            let body_ty = type_of_inner(body.clone(), &new_var_stack, infers)?;
            term_ref!(forall var_ty, body_ty)
        }
        Term::Var { index } => var_ty_stack
            .iter()
            .rev()
            .nth(*index)
            .ok_or(BadTerm)?
            .clone(),
        Term::Number { .. } => term_ref!(axiom "ℤ".to_string(), universe 0),
        Term::App { func, op } => {
            let op_ty = type_of_inner(op.clone(), var_ty_stack, infers)?;
            let func_type = type_of_inner(func.clone(), var_ty_stack, infers)?;
            let (var_ty, body) = match func_type.as_ref() {
                Term::Forall(Abstraction { var_ty, body }) => (var_ty, body),
                _ => return Err(IsNotFunc),
            };
            match_and_infer(var_ty.clone(), op_ty, infers)?;
            subst(body.clone(), op.clone())
        }
        Term::Wild { index } => infers.type_of(*index),
    })
}

pub fn type_of_and_infer(term: TermRef, infers: &mut InferResults) -> Result<TermRef> {
    type_of_inner(term, &[], infers)
}
