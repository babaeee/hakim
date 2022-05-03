use super::subtype_and_infer;
use super::{
    fill_wild, increase_foreign_vars, normalize, predict_wild, remove_unused_var, subst, Error::*,
    Result, Term, TermRef,
};
use crate::library::prelude;
use crate::{app_ref, Abstraction};
use crate::{brain::get_universe, term_ref};

use std::cmp::max;
use std::iter::once;

#[derive(Debug, Clone)]
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
            terms.push(TermRef::new(Term::Wild { index, scope: 0 }))
        }
        for index in n..2 * n {
            tys.push(TermRef::new(Term::Wild { index, scope: 0 }))
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
    fn get_with_scope(&self, i: usize, scope: usize) -> TermRef {
        let mut r = self.get(i);
        for _ in 0..scope {
            r = increase_foreign_vars(r, 0);
        }
        r
    }
    fn is_unknown(&self, i: usize) -> bool {
        *self.get(i) == Term::Wild { index: i, scope: 0 }
    }

    fn set(&mut self, i: usize, term: TermRef) -> Result<()> {
        let term_clone = term.clone();
        if i < self.n {
            self.terms[i] = term;
        } else {
            self.tys[i - self.n] = term;
        }
        // TODO: We should build the graph of dependencies between variables to just
        // update things that will change, not everything
        for _ in 0..self.n {
            self.relax();
        }
        let has_loop = self
            .terms
            .iter()
            .enumerate()
            .all(|(i, x)| *x == term_ref!(_ i) || !predict_wild(x, &|j, _| i == j))
            && self.tys.iter().enumerate().all(|(i, x)| {
                *x == term_ref!(_ i + self.n) || !predict_wild(x, &|j, _| i + self.n == j)
            });
        if has_loop {
            Ok(())
        } else {
            Err(LoopOfInference(i, term_clone))
        }
    }
    fn set_with_scope(&mut self, i: usize, scope: usize, term: TermRef) -> Result<()> {
        let mut t = term;
        for _ in 0..scope {
            match remove_unused_var(t, 0) {
                Some(x) => t = x,
                None => return Err(WildNeedLocalVar(i)),
            }
        }
        self.set(i, t)
    }

    fn type_of(&self, i: usize) -> TermRef {
        if i < self.n {
            self.tys[i].clone()
        } else {
            // TODO: this can be more general
            prelude::u()
        }
    }
    fn type_of_with_scope(&self, i: usize, scope: usize) -> TermRef {
        let mut r = self.type_of(i);
        for _ in 0..scope {
            r = increase_foreign_vars(r, 0);
        }
        r
    }
    pub fn fill(&self, term: TermRef) -> TermRef {
        fill_wild(term, &|i, s| self.get_with_scope(i, s))
    }

    fn relax(&mut self) {
        self.terms = self.terms.iter().map(|x| self.fill(x.clone())).collect();
        self.tys = self.tys.iter().map(|x| self.fill(x.clone())).collect();
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
    fn is_wild(t: &Term) -> Option<(usize, usize)> {
        if let Term::Wild { index, scope } = t {
            Some((*index, *scope))
        } else {
            None
        }
    }
    fn match_wild(i: usize, scope: usize, t: TermRef, infers: &mut InferResults) -> Result<()> {
        if infers.is_unknown(i) {
            infers.set_with_scope(i, scope, t)
        } else {
            match_and_infer_without_normalize(infers.get_with_scope(i, scope), t, infers)
        }
    }
    fn func_is_wild(t: &Term) -> bool {
        if let Term::App { func, .. } = t {
            if is_wild(func).is_some() {
                true
            } else {
                func_is_wild(func)
            }
        } else {
            false
        }
    }
    fn match_wild_func(wild_func: &Term, exp: TermRef, infers: &mut InferResults) -> Result<()> {
        // here we handle matching ?w f1 with an expression containing f1. This is
        // useful in infering induction. Since ?w can not contain foriegn variables, it
        // can be determined uniquely.
        if let Term::App { func, op } = wild_func {
            let (wild, scope) = if let Term::Wild { index, scope } = func.as_ref() {
                if !infers.is_unknown(*index) {
                    return Ok(());
                } else {
                    (*index, *scope)
                }
            } else {
                return Ok(());
            };
            let var = if let Term::Var { index } = op.as_ref() {
                *index
            } else {
                return Ok(());
            };
            if var < scope {
                // in this case wild can contain the variable, so we can not determine
                // function uniquely
                return Ok(());
            }
            let var_ty = if let Term::Forall(x) = infers.type_of(wild).as_ref() {
                x.var_ty.clone()
            } else {
                // I think it should always infer the type of functions.
                panic!("Fail in inference");
            };
            let fbody = if var == 0 {
                exp
            } else {
                replace_var(exp, 0, var)
            };
            infers.set(wild, term_ref!(fun var_ty, fbody))?;
        }
        fn replace_var(exp: TermRef, depth: usize, var: usize) -> TermRef {
            fn for_abs(abs: Abstraction, depth: usize, var: usize) -> Abstraction {
                let var_ty = replace_var(abs.var_ty, depth, var);
                let body = replace_var(abs.body, depth + 1, var + 1);
                Abstraction {
                    var_ty,
                    body,
                    hint_name: abs.hint_name,
                }
            }
            match exp.as_ref() {
                Term::Var { index } => {
                    let i = *index;
                    TermRef::new(Term::Var {
                        index: if i == var {
                            depth
                        } else if depth <= i && i < var {
                            i + 1
                        } else {
                            i
                        },
                    })
                }
                Term::Axiom { .. }
                | Term::Universe { .. }
                | Term::Number { .. }
                | Term::Wild { .. } => exp,
                Term::Forall(a) => TermRef::new(Term::Forall(for_abs(a.clone(), depth, var))),
                Term::Fun(a) => TermRef::new(Term::Fun(for_abs(a.clone(), depth, var))),
                Term::App { func, op } => TermRef::new(Term::App {
                    func: replace_var(func.clone(), depth, var),
                    op: replace_var(op.clone(), depth, var),
                }),
            }
        }
        Ok(())
    }
    if let Some((i, scope)) = is_wild(&t1) {
        return match_wild(i, scope, t2, infers);
    }
    if let Some((i, scope)) = is_wild(&t2) {
        return match_wild(i, scope, t1, infers);
    }
    if func_is_wild(&t1) {
        return match_wild_func(&t1, t2, infers);
    }
    if func_is_wild(&t2) {
        return match_wild_func(&t2, t1, infers);
    }
    match (t1.as_ref(), t2.as_ref()) {
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
        (Term::Fun(a), _) | (_, Term::Fun(a)) => {
            let f = match t1.as_ref() {
                Term::Fun(_) => t2.clone(),
                _ => t1.clone(),
            };
            // we try λ x: f x instead of f
            match_and_infer_without_normalize(
                app_ref!(increase_foreign_vars(f, 0), term_ref!(v 0)),
                a.body.clone(),
                infers,
            )
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
    let r = match term.as_ref() {
        Term::Axiom { ty, .. } => ty.clone(),
        Term::Universe { index } => TermRef::new(Term::Universe { index: index + 1 }),
        Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) => {
            let vtt = get_universe(type_of_inner(var_ty.clone(), var_ty_stack, infers)?)?;
            let new_var_stack = var_ty_stack
                .iter()
                .chain(once(var_ty))
                .map(|x| increase_foreign_vars(x.clone(), 0))
                .collect::<Vec<_>>();
            let body_ty = get_universe(type_of_inner(body.clone(), &new_var_stack, infers)?)?;
            term_ref!(universe max(vtt, body_ty))
        }
        Term::Fun(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) => {
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
            .ok_or_else(|| ForiegnVariableInTerm(index - var_ty_stack.len()))?
            .clone(),
        Term::Number { .. } => term_ref!(axiom "ℤ".to_string(), universe 0),
        Term::App { func, op } => {
            let op_ty = type_of_inner(op.clone(), var_ty_stack, infers)?;
            let func_type = type_of_inner(func.clone(), var_ty_stack, infers)?;
            let func_type = normalize(func_type);
            let (var_ty, body) = match func_type.as_ref() {
                Term::Forall(Abstraction {
                    var_ty,
                    body,
                    hint_name: _,
                }) => (var_ty, body),
                _ => {
                    return Err(IsNotFunc {
                        value: func.clone(),
                        ty: func_type,
                    })
                }
            };
            subtype_and_infer(op_ty, var_ty.clone(), infers)?;
            subst(body.clone(), op.clone())
        }
        Term::Wild { index, scope } => infers.type_of_with_scope(*index, *scope),
    };
    Ok(r)
}

pub fn type_of_and_infer(term: TermRef, infers: &mut InferResults) -> Result<TermRef> {
    type_of_inner(term, &[], infers)
}
