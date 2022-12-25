use std::collections::HashMap;
use std::fmt::Debug;

use crate::brain::detect::{detect_list_ty, detect_r_ty, detect_z_ty};
use crate::brain::{self, definitely_inequal, increase_foreign_vars, remove_unused_var, type_of};
use crate::library::prelude::{cnt, len1, mult, plus, pow, sigma, z};
use crate::{app_ref, brain::Term, term_ref, TermRef};
use num_bigint::{BigInt, Sign};
use typed_arena::Arena;

#[derive(Debug, Clone)]
pub enum ArithTree<'a, N> {
    Atom(TermRef),
    Const(N),
    Plus(&'a ArithTree<'a, N>, &'a ArithTree<'a, N>),
    Mult(&'a ArithTree<'a, N>, &'a ArithTree<'a, N>),
    Div(&'a ArithTree<'a, N>, &'a ArithTree<'a, N>),
}

use ArithTree::*;

#[derive(Clone, PartialEq, Eq)]
pub struct Poly<N>(N, Vec<(N, Vec<TermRef>)>);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rati<N>(pub Poly<N>, pub Poly<N>);

impl<N: Debug> Debug for Poly<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (a, x) in &self.1 {
            write!(f, "+ {:?} * {:?}", a, x)?;
        }
        Ok(())
    }
}

pub trait ConstRepr:
    Clone
    + std::ops::Add<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::ops::Neg<Output = Self>
    + std::cmp::PartialEq
    + std::cmp::PartialOrd
    + From<i32>
    + TryInto<i32>
    + Default
    + Debug
    + 'static
{
    fn from_term(term: &Term) -> Option<Self>;
    fn into_term(self) -> TermRef;
    fn mult_inverse(self) -> Self;
}

impl ConstRepr for BigInt {
    fn from_term(term: &Term) -> Option<Self> {
        match term {
            Term::Number { value } => Some(value.clone()),
            _ => None,
        }
    }

    fn into_term(self) -> TermRef {
        term_ref!(n self)
    }

    fn mult_inverse(self) -> Self {
        // Z doesn't support division
        unreachable!()
    }
}

/// merge two vector with DSU optimization: put smaller in larger to archive O(nlg(n)) amortized
fn unordered_concat<T>(mut v1: Vec<T>, mut v2: Vec<T>) -> Vec<T> {
    if v1.len() < v2.len() {
        v2.append(&mut v1);
        v2
    } else {
        v1.append(&mut v2);
        v1
    }
}

impl<N: std::ops::Add<Output = N>> std::ops::Add for Poly<N> {
    type Output = Poly<N>;

    fn add(self, rhs: Self) -> Self::Output {
        let c = self.0 + rhs.0;
        let v = unordered_concat(self.1, rhs.1);
        Poly(c, v)
    }
}

type ArithArena<'a, N> = &'a Arena<ArithTree<'a, N>>;

#[derive(Debug, Default)]
pub struct LinearPolyBuilder(HashMap<Vec<TermRef>, usize>);
pub struct LinearPoly<N>(N, Vec<(N, usize)>);

impl<N: Clone> LinearPoly<N> {
    pub fn from_slice(s: impl Iterator<Item = Poly<N>>) -> (usize, Vec<LinearPoly<N>>) {
        let mut builder = LinearPolyBuilder::default();
        let r = s.map(|x| builder.convert_poly(x)).collect();
        (builder.0.len(), r)
    }

    pub fn variables(&self) -> &[(N, usize)] {
        &self.1
    }

    pub fn constant(&self) -> &N {
        &self.0
    }
}

impl LinearPolyBuilder {
    fn get_id(&mut self, terms: Vec<TermRef>) -> usize {
        if let Some(id) = self.0.get(&terms) {
            *id
        } else {
            let id = self.0.len();
            self.0.insert(terms, id);
            id
        }
    }

    pub fn convert_poly<N>(&mut self, poly: Poly<N>) -> LinearPoly<N> {
        LinearPoly(
            poly.0,
            poly.1
                .into_iter()
                .map(|(c, t)| (c, self.get_id(t)))
                .collect(),
        )
    }
}

fn normalize<'a, N: ConstRepr>(
    tree: &'a ArithTree<'a, N>,
    arena: ArithArena<'a, N>,
    should_be_non_zero: &mut Vec<Poly<N>>,
) -> &'a ArithTree<'a, N> {
    match tree {
        Atom(_) | Const(_) => tree,
        Plus(Const(x), Const(y)) => arena.alloc(Const(x.clone() + y.clone())),
        Mult(Const(x), Const(y)) => arena.alloc(Const(x.clone() * y.clone())),
        Div(x, Const(y)) => normalize(
            arena.alloc(Mult(x, arena.alloc(Const(y.clone().mult_inverse())))),
            arena,
            should_be_non_zero,
        ),
        Div(a, b) => {
            let a = normalize(a, arena, should_be_non_zero);
            let b = normalize(b, arena, should_be_non_zero);
            if let Div(x, y) = a {
                let yb = normalize(arena.alloc(Mult(y, b)), arena, should_be_non_zero);
                return normalize(arena.alloc(Div(x, yb)), arena, should_be_non_zero);
            }
            if let Div(x, y) = b {
                let ya = normalize(arena.alloc(Mult(y, a)), arena, should_be_non_zero);
                return normalize(arena.alloc(Div(ya, x)), arena, should_be_non_zero);
            }
            arena.alloc(Div(a, b))
        }
        Plus(a, b) => {
            let a = normalize(a, arena, should_be_non_zero);
            let b = normalize(b, arena, should_be_non_zero);
            match (a, b) {
                (Div(x, y), t) | (t, Div(x, y)) => {
                    should_be_non_zero.push(normal_tree_to_poly(y));
                    normalize(
                        arena.alloc(Div(arena.alloc(Plus(arena.alloc(Mult(y, t)), x)), y)),
                        arena,
                        should_be_non_zero,
                    )
                }
                _ => arena.alloc(Plus(a, b)),
            }
        }
        Mult(a, b) => {
            let a = normalize(a, arena, should_be_non_zero);
            let b = normalize(b, arena, should_be_non_zero);
            if let Plus(x, y) = a {
                let xb = normalize(arena.alloc(Mult(x, b)), arena, should_be_non_zero);
                let yb = normalize(arena.alloc(Mult(y, b)), arena, should_be_non_zero);
                return normalize(arena.alloc(Plus(xb, yb)), arena, should_be_non_zero);
            }
            if let Plus(x, y) = b {
                let xa = normalize(arena.alloc(Mult(x, a)), arena, should_be_non_zero);
                let ya = normalize(arena.alloc(Mult(y, a)), arena, should_be_non_zero);
                return normalize(arena.alloc(Plus(xa, ya)), arena, should_be_non_zero);
            }
            match (a, b) {
                (Div(x, y), t) | (t, Div(x, y)) => normalize(
                    arena.alloc(Div(arena.alloc(Mult(x, t)), y)),
                    arena,
                    should_be_non_zero,
                ),
                _ => arena.alloc(Mult(a, b)),
            }
        }
    }
}

fn pow_to_arith<N: ConstRepr>(
    op1: TermRef,
    op2: TermRef,
    arena: ArithArena<'_, N>,
) -> ArithTree<'_, N> {
    if let Term::Number { value } = op1.as_ref() {
        if *value == BigInt::from(1i32) {
            return Const(1i32.into());
        }
    }
    if let Term::Number { value } = op2.as_ref() {
        if value.sign() == Sign::Minus {
            return Const(0i32.into());
        }
        if *value < 5i32.into() {
            let v = value.try_into().unwrap();
            let mut r = Const(1i32.into());
            let op1a = term_ref_to_arith(op1, arena);
            for _ in 0i32..v {
                r = Mult(op1a, arena.alloc(r));
            }
            return r;
        }
    }
    atom_normalizer(app_ref!(pow(), op1, op2))
}

fn cnt_to_arith<N: ConstRepr>(
    ty: TermRef,
    arg: TermRef,
    l: TermRef,
    arena: ArithArena<'_, N>,
) -> &ArithTree<'_, N> {
    if let Term::App { func, op: op2 } = l.as_ref() {
        match func.as_ref() {
            Term::Axiom { unique_name, .. } => {
                if unique_name == "nil" {
                    return arena.alloc(Const(0i32.into()));
                }
            }
            Term::App { func, op: op1 } => {
                if let Term::App { func, op: list_ty } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        match unique_name.as_str() {
                            "cons" => {
                                let r = cnt_to_arith(ty.clone(), arg.clone(), op2.clone(), arena);
                                if arg == *op1 {
                                    return arena.alloc(Plus(arena.alloc(Const(1i32.into())), r));
                                }
                                if definitely_inequal(&arg, op1) {
                                    return r;
                                }
                            }
                            "plus" if detect_list_ty(list_ty).is_some() => {
                                let a = cnt_to_arith(ty.clone(), arg.clone(), op2.clone(), arena);
                                let b = cnt_to_arith(ty, arg, op1.clone(), arena);
                                return arena.alloc(Plus(a, b));
                            }
                            _ => (),
                        }
                    }
                }
            }
            _ => (),
        }
    }
    arena.alloc(atom_normalizer(app_ref!(cnt(), ty, l, arg)))
}

fn len1_to_arith<N: ConstRepr>(
    ty: TermRef,
    arg: TermRef,
    arena: ArithArena<'_, N>,
) -> &ArithTree<'_, N> {
    if let Term::App { func, op: op2 } = arg.as_ref() {
        match func.as_ref() {
            Term::Axiom { unique_name, .. } => {
                if unique_name == "nil" || unique_name == "set_empty" {
                    return arena.alloc(Const(0i32.into()));
                }
            }
            Term::App { func, op: op1 } => {
                if let Term::App { func, op: list_ty } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        match unique_name.as_str() {
                            "cons" => {
                                let r = len1_to_arith(ty, op2.clone(), arena);
                                return arena.alloc(Plus(arena.alloc(Const(1i32.into())), r));
                            }
                            "plus" if detect_list_ty(list_ty).is_some() => {
                                let a = len1_to_arith(ty.clone(), op2.clone(), arena);
                                let b = len1_to_arith(ty, op1.clone(), arena);
                                return arena.alloc(Plus(a, b));
                            }
                            _ => (),
                        }
                    }
                }
            }
            _ => (),
        }
    }
    arena.alloc(atom_normalizer(app_ref!(len1(), ty, arg)))
}

pub trait SigmaSimplifier: Copy {
    type T;
    fn handle_sigma_atom(self, r: TermRef, f: TermRef) -> Self::T;
    fn minus(self, x: Self::T, y: Self::T) -> Self::T;
    fn mult(self, x: Self::T, y: Self::T) -> Self::T;
    fn plus(self, x: Self::T, y: Self::T) -> Self::T;
    fn handle_term(self, t: TermRef) -> Self::T;
}

impl<'a, N: ConstRepr> SigmaSimplifier for ArithArena<'a, N> {
    type T = &'a ArithTree<'a, N>;

    fn handle_sigma_atom(self, r: TermRef, f: TermRef) -> Self::T {
        self.alloc(Atom(app_ref!(sigma(), term_ref!(n 0), r, f)))
    }

    fn minus(self, x: Self::T, y: Self::T) -> Self::T {
        self.alloc(minus(x, y, self))
    }

    fn mult(self, x: Self::T, y: Self::T) -> Self::T {
        self.alloc(Mult(x, y))
    }

    fn plus(self, x: Self::T, y: Self::T) -> Self::T {
        self.alloc(Plus(x, y))
    }

    fn handle_term(self, t: TermRef) -> Self::T {
        term_ref_to_arith(t, self)
    }
}

pub fn sigma_to_arith<S: SigmaSimplifier, N: ConstRepr>(
    l: TermRef,
    r: TermRef,
    f: TermRef,
    simplifier: S,
) -> S::T {
    fn phase2<S: SigmaSimplifier, N: ConstRepr>(r: TermRef, f: TermRef, simplifier: S) -> S::T {
        if let Term::Fun(abs) = f.as_ref() {
            let body = Poly::<N>::from(abs.body.clone());
            let ra = simplifier.handle_term(r.clone());
            let mut result = simplifier.mult(
                simplifier.handle_term(body.constant().clone().into_term()),
                ra,
            );
            for (x, v) in body.variables() {
                let mut rstmp = simplifier.handle_term(x.clone().into_term());
                let mut deps: Option<TermRef> = None;
                for x in v {
                    if let Some(x) = remove_unused_var(x.clone()) {
                        rstmp = simplifier.mult(rstmp, simplifier.handle_term(x.clone()));
                    } else {
                        deps = Some(match deps {
                            Some(y) => app_ref!(mult(), z(), x, y),
                            None => x.clone(),
                        });
                    }
                }
                if let Some(deps) = deps {
                    rstmp = simplifier.mult(
                        rstmp,
                        simplifier.handle_sigma_atom(r.clone(), term_ref!(fun z(), deps)),
                    );
                }
                result = simplifier.plus(result, rstmp);
            }
            result
        } else {
            let f = increase_foreign_vars(f);
            let f = app_ref!(f, term_ref!(v 0));
            let f = term_ref!(fun z(), f);
            phase2::<S, N>(r, f, simplifier)
        }
    }
    if l != term_ref!(n 0) {
        return simplifier.minus(
            sigma_to_arith::<S, N>(term_ref!(n 0), r, f.clone(), simplifier),
            sigma_to_arith::<S, N>(term_ref!(n 0), l, f, simplifier),
        );
    }
    let rp = Poly::<N>::from(r);
    let rpc = rp.constant();
    if *rpc > 5i32.into() || *rpc < (-5i32).into() {
        return phase2::<S, N>(rp.into_term(), f, simplifier);
    }
    let Ok(rpc): Result<i32, _> = rpc.clone().try_into() else {
        todo!()
    };
    let mut t = if rp.variables().is_empty() {
        simplifier.handle_term(term_ref!(n 0))
    } else {
        phase2::<S, N>(rp.with_constant(0).into_term(), f.clone(), simplifier)
    };
    for i in 0..rpc {
        let f_i = brain::normalize(app_ref!(f, rp.with_constant(i).into_term()));
        t = simplifier.plus(t, simplifier.handle_term(f_i));
    }
    for i in rpc..0 {
        let f_i = brain::normalize(app_ref!(f, rp.with_constant(i).into_term()));
        t = simplifier.minus(t, simplifier.handle_term(f_i));
    }
    t
}

fn atom_normalizer<N: ConstRepr>(t: TermRef) -> ArithTree<'static, N> {
    fn f<N: ConstRepr>(t: TermRef) -> TermRef {
        match t.as_ref() {
            Term::App { func, op } => {
                let op = if type_of(op.clone()) == Ok(z()) {
                    Poly::<N>::from(op.clone()).into_term()
                } else {
                    f::<N>(op.clone())
                };
                let func = f::<N>(func.clone());
                app_ref!(func, op)
            }
            _ => t,
        }
    }
    Atom(f::<N>(t))
}

fn term_ref_to_arith<N: ConstRepr>(t: TermRef, arena: ArithArena<'_, N>) -> &ArithTree<'_, N> {
    if let Some(x) = N::from_term(&t) {
        return arena.alloc(Const(x));
    }
    let arith_tree = match t.as_ref() {
        Term::App { func, op: op2 } => match func.as_ref() {
            Term::App { func, op: op1 } => match func.as_ref() {
                Term::App { func, op } => match func.as_ref() {
                    Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                        "sigma" => {
                            return sigma_to_arith::<_, N>(
                                op.clone(),
                                op1.clone(),
                                op2.clone(),
                                arena,
                            );
                        }
                        "cnt" => {
                            return cnt_to_arith(op.clone(), op1.clone(), op2.clone(), arena);
                        }
                        "plus" if detect_z_ty(op) || detect_r_ty(op) => Plus(
                            term_ref_to_arith(op1.clone(), arena),
                            term_ref_to_arith(op2.clone(), arena),
                        ),
                        "mult" if detect_z_ty(op) || detect_r_ty(op) => Mult(
                            term_ref_to_arith(op1.clone(), arena),
                            term_ref_to_arith(op2.clone(), arena),
                        ),
                        "div" if detect_z_ty(op) || detect_r_ty(op) => Div(
                            term_ref_to_arith(op1.clone(), arena),
                            term_ref_to_arith(op2.clone(), arena),
                        ),
                        _ => atom_normalizer(t),
                    },
                    _ => atom_normalizer(t),
                },
                Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                    "minus" => minus(
                        term_ref_to_arith(op1.clone(), arena),
                        term_ref_to_arith(op2.clone(), arena),
                        arena,
                    ),
                    "pow" => pow_to_arith(op1.clone(), op2.clone(), arena),
                    "len1" => return len1_to_arith(op1.clone(), op2.clone(), arena),
                    _ => atom_normalizer(t),
                },
                _ => atom_normalizer(t),
            },
            //            Term::Axiom { unique_name, .. } => match unique_name.as_str() {
            //                "chr" => {
            //                    definitely_inequal(t1, t2)
            //                    term_ref_to_arith(op2.clone(), arena), //Todo add mod to term
            //                },
            //               _ => atom_normalizer(t),
            //            },
            _ => atom_normalizer(t),
        },
        _ => atom_normalizer(t),
    };
    arena.alloc(arith_tree)
}

fn minus<'a, N: ConstRepr>(
    op1: &'a ArithTree<'a, N>,
    op2: &'a ArithTree<'a, N>,
    arena: ArithArena<'a, N>,
) -> ArithTree<'a, N> {
    Plus(op1, arena.alloc(Mult(arena.alloc(Const((-1).into())), op2)))
}

fn normal_tree_to_poly<N: ConstRepr>(x: &ArithTree<'_, N>) -> Poly<N> {
    fn sorter<N: ConstRepr>(x: Poly<N>) -> Poly<N> {
        let Poly(c, mut v) = x;
        for e in &mut v {
            e.1.sort();
        }
        v.sort_by(|a, b| a.1.cmp(&b.1));
        let mut ss = vec![];
        let mut iter = v.into_iter();
        let (mut k, mut x) = match iter.next() {
            Some(f) => f,
            None => return Poly(c, vec![]),
        };
        let mut ins = |k, x| {
            if k == 0.into() {
                return;
            }
            ss.push((k, x));
        };
        for (k2, x2) in iter {
            if x == x2 {
                k = k + k2;
            } else {
                ins(k, x);
                k = k2;
                x = x2;
            }
        }
        ins(k, x);
        Poly(c, ss)
    }
    fn tree_to_d2<N: ConstRepr>(tree: &ArithTree<'_, N>) -> Poly<N> {
        match tree {
            Atom(t) => Poly(0.into(), vec![(1.into(), vec![t.clone()])]),
            Const(i) => Poly(i.clone(), vec![]),
            Plus(t1, t2) => tree_to_d2(t1) + tree_to_d2(t2),
            Mult(t1, t2) => {
                fn to_mul<N: ConstRepr>(x: &ArithTree<'_, N>) -> (N, Vec<TermRef>) {
                    let Poly(c1, mut r1) = tree_to_d2(x);
                    if r1.is_empty() {
                        return (c1, vec![]);
                    }
                    if r1.len() != 1 || c1 != 0.into() {
                        panic!("tree is not normalized. this is a bug");
                    }
                    r1.pop().unwrap()
                }
                let (c1, r1) = to_mul(t1);
                let (c2, r2) = to_mul(t2);
                if r1.is_empty() && r2.is_empty() {
                    return Poly(c1 * c2, vec![]);
                }
                Poly(0.into(), vec![(c1 * c2, unordered_concat(r1, r2))])
            }
            Div(..) => unreachable!(),
        }
    }
    sorter(tree_to_d2(x))
}

impl<N: ConstRepr> From<TermRef> for Poly<N> {
    fn from(t: TermRef) -> Self {
        let arena = &Arena::new();
        let a = normalize(term_ref_to_arith(t, arena), arena, &mut vec![]);
        normal_tree_to_poly(a)
    }
}

impl<N: ConstRepr> Rati<N> {
    pub fn from_subtract(t1: TermRef, t2: TermRef) -> (Self, Vec<Poly<N>>) {
        let arena = &Arena::with_capacity(32);
        let a = arith_tree_of_substract::<N>(t1, arena, t2);
        let mut oblications = vec![];
        let a = normalize(a, arena, &mut oblications);
        let (soorat, makhraj) = match a {
            Div(x, y) => (*x, *y),
            _ => (a, &*arena.alloc(Const(1.into()))),
        };
        (
            Rati(normal_tree_to_poly(soorat), normal_tree_to_poly(makhraj)),
            oblications,
        )
    }
}

impl<N: ConstRepr> Poly<N> {
    fn into_term(self) -> TermRef {
        let mut t = self.0.into_term();
        for (c, var_list) in self.1 {
            let mut tx = c.into_term();
            for var in var_list {
                tx = app_ref!(mult(), z(), tx, var);
            }
            t = app_ref!(plus(), z(), t, tx);
        }
        t
    }

    pub fn from_subtract(t1: TermRef, t2: TermRef) -> Self {
        let arena = &Arena::with_capacity(32);
        let a = normalize(arith_tree_of_substract(t1, arena, t2), arena, &mut vec![]);
        normal_tree_to_poly(a)
    }

    pub fn constant(&self) -> &N {
        &self.0
    }

    pub fn set_constant(&mut self, i: i32) {
        self.0 = i.into();
    }

    pub fn with_constant(&self, i: i32) -> Self {
        let mut c = self.clone();
        c.set_constant(i);
        c
    }

    pub fn variables(&self) -> &[(N, Vec<TermRef>)] {
        &self.1
    }

    pub fn is_zero(&self) -> bool {
        *self.constant() == 0.into() && self.variables().is_empty()
    }

    pub fn negate(&mut self) {
        self.0 = -std::mem::take(&mut self.0);
        for x in &mut self.1 {
            x.0 = -std::mem::take(&mut x.0);
        }
    }

    pub fn add(&mut self, num: N) {
        self.0 = self.0.clone() + num;
    }
}

fn arith_tree_of_substract<N: ConstRepr>(
    t1: TermRef,
    arena: ArithArena<'_, N>,
    t2: TermRef,
) -> &ArithTree<'_, N> {
    let a1 = term_ref_to_arith(t1, arena);
    let a2 = term_ref_to_arith(t2, arena);
    let m1 = arena.alloc(Const((-1).into()));
    let neg_a2 = arena.alloc(Mult(m1, a2));
    let a = arena.alloc(Plus(a1, neg_a2));
    a
}
