use super::{
    fill_wild, increase_foreign_vars, normalize, predict_wild, subst, ErrorContext::*,
    ErrorReason::*, Result, Term, TermRef,
};
use super::{map_foreign_vars, subtype_and_infer};
use crate::{app_ref, term_ref, Abstraction};

use std::cmp::max;
use std::iter::once;

#[derive(Debug, Clone)]
pub struct Obligation {
    pub var: usize,
    pub eq: (TermRef, TermRef),
}

#[derive(Debug, Clone)]
pub struct InferResults {
    pub n: usize,
    pub terms: Vec<TermRef>,
    pub tys: Vec<TermRef>,
    pub unresolved_obligations: Vec<Obligation>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum VarCategory {
    Term(usize),
    Ty(usize),
}

pub const RESERVED_SPACE: usize = 2;

impl From<usize> for VarCategory {
    fn from(i: usize) -> Self {
        if i % RESERVED_SPACE == 0 {
            VarCategory::Term(i / RESERVED_SPACE)
        } else {
            VarCategory::Ty(i / RESERVED_SPACE)
        }
    }
}

impl VarCategory {
    pub fn to_term(self, scope: Option<Vec<usize>>) -> TermRef {
        let index = self.to_index();
        TermRef::new(Term::Wild { index, scope })
    }

    fn to_index(self) -> usize {
        match self {
            VarCategory::Term(i) => RESERVED_SPACE * i,
            VarCategory::Ty(i) => RESERVED_SPACE * i + 1,
        }
    }
}

impl InferResults {
    pub fn new(n: usize) -> InferResults {
        let mut terms = vec![];
        let mut tys = vec![];
        for i in 0..n {
            terms.push(VarCategory::Term(i).to_term(None));
            tys.push(VarCategory::Ty(i).to_term(None));
        }
        InferResults {
            terms,
            tys,
            n,
            unresolved_obligations: vec![],
        }
    }

    /// adds a variable which can not contain foreign bindings
    pub fn add_var_top_level(&mut self) -> TermRef {
        self.add_var_with_scope(Some(vec![]))
    }

    pub fn add_var_with_scope(&mut self, scope: Option<Vec<usize>>) -> TermRef {
        let r = VarCategory::Term(self.n).to_term(scope.clone());
        self.terms.push(r.clone());
        self.tys.push(VarCategory::Ty(self.n).to_term(scope));
        self.n += 1;
        r
    }

    pub fn get(&self, i: usize) -> TermRef {
        match VarCategory::from(i) {
            VarCategory::Term(i) => self.terms[i].clone(),
            VarCategory::Ty(i) => self.tys[i].clone(),
        }
    }
    fn get_with_scope(&self, i: usize, scope: &[usize]) -> Result<TermRef> {
        let term = self.get(i);
        if let Term::Wild { index, scope: None } = term.as_ref() {
            return Ok(TermRef::new(Term::Wild {
                index: *index,
                scope: Some(scope.into()),
            }));
        }
        let mut need_var = false;
        let r = map_foreign_vars(term, |x, is_var| match scope.get(x) {
            Some(k) => *k,
            None => {
                if is_var {
                    need_var = true;
                }
                2000000
            }
        });
        if need_var {
            dbg!(&r);
            return Err(WildNeedLocalVar(i).into());
        }
        Ok(r)
    }
    fn is_unknown(&self, i: usize) -> bool {
        matches!(self.get(i).as_ref(), Term::Wild { index, .. } if *index == i)
    }

    fn set(&mut self, i: usize, term: TermRef) -> Result<()> {
        let term_clone = term.clone();
        match VarCategory::from(i) {
            VarCategory::Term(i) => self.terms[i] = term,
            VarCategory::Ty(i) => self.tys[i] = term,
        }
        // TODO: We should build the graph of dependencies between variables to just
        // update things that will change, not everything
        for _ in 0..self.n {
            self.relax()?;
        }
        let mut loop_free = true;
        for x in 0..RESERVED_SPACE * self.n {
            let t = self.get(x);
            if !matches!(t.as_ref(), Term::Wild { index, .. } if *index == x)
                && predict_wild(&t, &|j, _| x == j)
            {
                loop_free = false;
            }
        }
        if loop_free {
            Ok(())
        } else {
            Err(LoopOfInference(i, term_clone).into())
        }
    }
    fn set_with_scope(&mut self, i: usize, scope: &[usize], term: TermRef) -> Result<()> {
        let mut need_var = false;
        let t = map_foreign_vars(term, |vi, is_var| {
            match scope.iter().enumerate().find(|x| *x.1 == vi) {
                Some((x, _)) => x,
                None => {
                    if is_var {
                        need_var = true;
                    }
                    100000000
                }
            }
        });
        if need_var {
            dbg!(&t);
            return Err(WildNeedLocalVar(i).into());
        }
        self.set(i, t)
    }

    fn type_of(&self, i: usize) -> TermRef {
        match VarCategory::from(i) {
            VarCategory::Term(i) => self.tys[i].clone(),
            VarCategory::Ty(_) => term_ref!(universe 0), // TODO: this can be more general
        }
    }
    fn type_of_with_scope(&self, i: usize, scope: &[usize]) -> Result<TermRef> {
        match VarCategory::from(i) {
            VarCategory::Term(i) => self.get_with_scope(VarCategory::Ty(i).to_index(), scope),
            VarCategory::Ty(_) => Ok(term_ref!(universe 0)), // TODO: this can be more general
        }
    }
    pub fn fill(&self, term: TermRef) -> Result<TermRef> {
        if let Term::Wild { scope: None, .. } = term.as_ref() {
            return Ok(term);
        }
        fill_wild(term, &|i, s| self.get_with_scope(i, s.unwrap()))
    }

    fn relax(&mut self) -> Result<()> {
        self.terms = self
            .terms
            .iter()
            .map(|x| self.fill(x.clone()))
            .collect::<Result<_>>()?;
        self.tys = self
            .tys
            .iter()
            .map(|x| self.fill(x.clone()))
            .collect::<Result<_>>()?;
        Ok(())
    }
}

fn match_wild(i: usize, scope: &[usize], t: TermRef, infers: &mut InferResults) -> Result<()> {
    if infers.is_unknown(i) {
        infers.set_with_scope(i, scope, t)
    } else {
        match_and_infer_without_normalize(infers.get_with_scope(i, scope)?, t, infers)
    }
}

fn match_and_infer_without_normalize(
    t1: TermRef,
    t2: TermRef,
    infers: &mut InferResults,
) -> Result<()> {
    fn main(t1: TermRef, t2: TermRef, infers: &mut InferResults) -> Result<()> {
        if let Some((i, scope)) = is_wild(&t1) {
            return match_wild(i, scope.unwrap(), t2, infers);
        }
        if let Some((i, scope)) = is_wild(&t2) {
            return match_wild(i, scope.unwrap(), t1, infers);
        }
        if let Some(w) = func_is_wild(&t1) {
            return match_wild_func(w.0, t1, t2, infers);
        }
        if let Some(w) = func_is_wild(&t2) {
            return match_wild_func(w.0, t2, t1, infers);
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
                main(func1.clone(), func2.clone(), infers)?;
                main(op1.clone(), op2.clone(), infers)
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
                    Err(TypeMismatch(t1, t2).into())
                }
            }
            (Term::Universe { index: i1 }, Term::Universe { index: i2 }) => {
                if i1 == i2 {
                    Ok(())
                } else {
                    Err(TypeMismatch(t1, t2).into())
                }
            }
            (Term::Number { value: i1 }, Term::Number { value: i2 }) => {
                if i1 == i2 {
                    Ok(())
                } else {
                    Err(TypeMismatch(t1, t2).into())
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
                main(
                    app_ref!(increase_foreign_vars(f), term_ref!(v 0)),
                    a.body.clone(),
                    infers,
                )
            }
            (Term::Var { index: i1 }, Term::Var { index: i2 }) => {
                if i1 == i2 {
                    Ok(())
                } else {
                    Err(TypeMismatch(t1, t2).into())
                }
            }
            _ => Err(TypeMismatch(t1, t2).into()),
        }
    }
    fn for_abs(a1: Abstraction, a2: Abstraction, infers: &mut InferResults) -> Result<()> {
        main(a1.var_ty, a2.var_ty, infers)?;
        main(a1.body, a2.body, infers)
    }
    fn is_wild(t: &Term) -> Option<(usize, Option<&[usize]>)> {
        if let Term::Wild { index, scope } = t {
            Some((*index, scope.as_deref()))
        } else {
            None
        }
    }
    fn func_is_wild(t: &Term) -> Option<(usize, Option<&[usize]>)> {
        if let Term::App { func, .. } = t {
            is_wild(func).or_else(|| func_is_wild(func))
        } else {
            None
        }
    }
    fn match_wild_func(
        wild: usize,
        wild_func: TermRef,
        exp: TermRef,
        infers: &mut InferResults,
    ) -> Result<()> {
        let mut unresolved = || {
            infers.unresolved_obligations.push(Obligation {
                var: wild,
                eq: (wild_func.clone(), exp.clone()),
            });
            Ok(())
        };
        // here we handle matching ?w f1 with an expression containing f1. This is
        // useful in infering induction. Since ?w can not contain foriegn variables, it
        // can be determined uniquely.
        if let Term::App { func, op } = wild_func.as_ref() {
            let (wild, scope) = if let Term::Wild { index, scope } = func.as_ref() {
                if !infers.is_unknown(*index) {
                    return Ok(());
                } else {
                    (*index, scope.clone())
                }
            } else {
                return unresolved();
            };
            let var = if let Term::Var { index } = op.as_ref() {
                *index
            } else {
                return Ok(());
            };
            if var < scope.map(|x| x.len()).unwrap_or(0) {
                // in this case wild can contain the variable, so we can not determine
                // function uniquely
                return Ok(());
            }
            let var_ty = match infers.type_of(wild).as_ref() {
                Term::Forall(x) => x.var_ty.clone(),
                Term::Wild { index, scope } => {
                    let a = infers.add_var_with_scope(scope.clone());
                    let b = infers.add_var_with_scope(
                        scope.as_ref().map(|x| x.iter().map(|x| x + 1).collect()),
                    );
                    infers.set_with_scope(
                        *index,
                        scope.as_deref().unwrap(),
                        term_ref!(forall a, b),
                    )?;
                    a
                }
                // I think it should always infer the type of functions.
                _ => unreachable!("Strange type appears in infer"),
            };
            let fbody = if var == 0 {
                exp
            } else {
                replace_var(exp, 0, var)
            };
            infers.set(wild, term_ref!(fun var_ty, fbody))?;
            return Ok(());
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
                | Term::NumberR { .. }
                | Term::Wild { .. } => exp,
                Term::Forall(a) => TermRef::new(Term::Forall(for_abs(a.clone(), depth, var))),
                Term::Fun(a) => TermRef::new(Term::Fun(for_abs(a.clone(), depth, var))),
                Term::App { func, op } => TermRef::new(Term::App {
                    func: replace_var(func.clone(), depth, var),
                    op: replace_var(op.clone(), depth, var),
                }),
            }
        }
        unresolved()
    }
    main(t1.clone(), t2.clone(), infers)
        .map_err(|e| e.with_context(InMatching(t1.clone(), t2.clone())))
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
    pub fn main(
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
                let vtt = get_universe_and_infer(
                    type_of_inner(var_ty.clone(), var_ty_stack, infers)?.as_ref(),
                    infers,
                )?;
                let new_var_stack = var_ty_stack
                    .iter()
                    .chain(once(var_ty))
                    .map(|x| increase_foreign_vars(x.clone()))
                    .collect::<Vec<_>>();
                let body_ty = get_universe_and_infer(
                    type_of_inner(body.clone(), &new_var_stack, infers)?.as_ref(),
                    infers,
                )?;
                term_ref!(universe max(vtt, body_ty))
            }
            Term::Fun(Abstraction {
                var_ty,
                body,
                hint_name: _,
            }) => {
                get_universe_and_infer(
                    type_of_inner(var_ty.clone(), var_ty_stack, infers)?.as_ref(),
                    infers,
                )?;
                let new_var_stack = var_ty_stack
                    .iter()
                    .chain(once(var_ty))
                    .map(|x| increase_foreign_vars(x.clone()))
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
            Term::NumberR { .. } => term_ref!(axiom "ℝ".to_string(), universe 0),
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
                        }
                        .into())
                    }
                };
                subtype_and_infer(op_ty, var_ty.clone(), infers)?;
                subst(body.clone(), op.clone())
            }
            Term::Wild { index, scope } => {
                infers.type_of_with_scope(*index, scope.as_ref().unwrap())?
            }
        };
        Ok(r)
    }
    main(term.clone(), var_ty_stack, infers).map_err(|e| e.with_context(InTypechecking(term)))
}

pub fn type_of_and_infer(term: TermRef, infers: &mut InferResults) -> Result<TermRef> {
    type_of_inner(term, &[], infers)
}

fn get_universe_and_infer(term: &Term, infers: &mut InferResults) -> Result<usize> {
    match term {
        Term::Universe { index } => Ok(*index),
        Term::Wild { index, scope } => {
            match_wild(
                *index,
                scope.as_deref().unwrap(),
                term_ref!(universe 0),
                infers,
            )?;
            Ok(0)
        }
        _ => Err(IsNotUniverse.into()),
    }
}
