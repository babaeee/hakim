use std::collections::HashMap;
use std::fmt::Debug;

use crate::brain::{self, definitely_inequal, increase_foreign_vars, remove_unused_var, type_of};
use crate::library::prelude::{cnt, len1, mult, plus, pow, sigma, z};
use crate::{app_ref, brain::Term, term_ref, TermRef};
use num_bigint::{BigInt, Sign};
use typed_arena::Arena;

#[derive(Debug, Clone)]
pub enum ArithTree<'a> {
    Atom(TermRef),
    Const(BigInt),
    Plus(&'a ArithTree<'a>, &'a ArithTree<'a>),
    Mult(&'a ArithTree<'a>, &'a ArithTree<'a>),
}

use ArithTree::*;

#[derive(Clone, PartialEq, Eq)]
pub struct Poly(BigInt, Vec<(BigInt, Vec<TermRef>)>);
impl Debug for Poly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (a, x) in &self.1 {
            write!(f, "+ {} * {:?}", a, x)?;
        }
        Ok(())
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

impl std::ops::Add for Poly {
    type Output = Poly;

    fn add(self, rhs: Self) -> Self::Output {
        let c = self.0 + rhs.0;
        let v = unordered_concat(self.1, rhs.1);
        Poly(c, v)
    }
}

type ArithArena<'a> = &'a Arena<ArithTree<'a>>;

#[derive(Debug, Default)]
pub struct LinearPolyBuilder(HashMap<Vec<TermRef>, usize>);
pub struct LinearPoly(BigInt, Vec<(BigInt, usize)>);

impl LinearPoly {
    pub fn from_slice(s: &[Poly]) -> (usize, Vec<LinearPoly>) {
        let mut builder = LinearPolyBuilder::default();
        let r = s.iter().cloned().map(|x| builder.convert_poly(x)).collect();
        (builder.0.len(), r)
    }

    pub fn variables(&self) -> &[(BigInt, usize)] {
        &self.1
    }

    pub fn constant(&self) -> &BigInt {
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

    pub fn convert_poly(&mut self, poly: Poly) -> LinearPoly {
        LinearPoly(
            poly.0,
            poly.1
                .into_iter()
                .map(|(c, t)| (c, self.get_id(t)))
                .collect(),
        )
    }
}

fn normalize<'a>(tree: &'a ArithTree<'a>, arena: ArithArena<'a>) -> &'a ArithTree<'a> {
    match tree {
        Atom(_) | Const(_) => tree,
        Plus(a, b) => arena.alloc(Plus(normalize(*a, arena), normalize(*b, arena))),
        Mult(a, b) => {
            let a = normalize(*a, arena);
            let b = normalize(*b, arena);
            if let Plus(x, y) = a {
                let xb = normalize(arena.alloc(Mult(x, b)), arena);
                let yb = normalize(arena.alloc(Mult(y, b)), arena);
                return arena.alloc(Plus(xb, yb));
            }
            if let Plus(x, y) = b {
                let xa = normalize(arena.alloc(Mult(x, a)), arena);
                let ya = normalize(arena.alloc(Mult(y, a)), arena);
                return arena.alloc(Plus(xa, ya));
            }
            arena.alloc(Mult(a, b))
        }
    }
}

fn tree_to_d2(tree: &ArithTree<'_>) -> Poly {
    match tree {
        Atom(t) => Poly(0.into(), vec![(1.into(), vec![t.clone()])]),
        Const(i) => Poly(i.clone(), vec![]),
        Plus(t1, t2) => tree_to_d2(*t1) + tree_to_d2(*t2),
        Mult(t1, t2) => {
            fn to_mul(x: &ArithTree<'_>) -> (BigInt, Vec<TermRef>) {
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
    }
}

fn pow_to_arith(op1: TermRef, op2: TermRef, arena: ArithArena<'_>) -> ArithTree<'_> {
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

fn cnt_to_arith(ty: TermRef, arg: TermRef, l: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
    if let Term::App { func, op: op2 } = l.as_ref() {
        match func.as_ref() {
            Term::Axiom { unique_name, .. } => {
                if unique_name == "nil" {
                    return arena.alloc(Const(0i32.into()));
                }
            }
            Term::App { func, op: op1 } => {
                if let Term::App { func, op: _ } = func.as_ref() {
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
                            "plus_list" => {
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

fn len1_to_arith(ty: TermRef, arg: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
    if let Term::App { func, op: op2 } = arg.as_ref() {
        match func.as_ref() {
            Term::Axiom { unique_name, .. } => {
                if unique_name == "nil" {
                    return arena.alloc(Const(0i32.into()));
                }
            }
            Term::App { func, op: op1 } => {
                if let Term::App { func, op: _ } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        match unique_name.as_str() {
                            "cons" => {
                                let r = len1_to_arith(ty, op2.clone(), arena);
                                return arena.alloc(Plus(arena.alloc(Const(1i32.into())), r));
                            }
                            "plus_list" => {
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

fn sigma_to_arith(l: TermRef, r: TermRef, f: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
    fn atom(r: TermRef, f: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
        arena.alloc(Atom(app_ref!(sigma(), term_ref!(n 0), r, f)))
    }
    fn phase2(r: TermRef, f: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
        if let Term::Fun(abs) = f.as_ref() {
            let body = Poly::from(abs.body.clone());
            let ra = term_ref_to_arith(r.clone(), arena);
            let mut result = arena.alloc(Mult(arena.alloc(Const(body.constant().clone())), ra));
            for (x, v) in body.variables() {
                let mut rstmp = arena.alloc(Const(x.clone()));
                let mut deps: Option<TermRef> = None;
                for x in v {
                    if let Some(x) = remove_unused_var(x.clone(), 0) {
                        rstmp = arena.alloc(Mult(rstmp, term_ref_to_arith(x.clone(), arena)));
                    } else {
                        deps = Some(match deps {
                            Some(y) => app_ref!(mult(), x, y),
                            None => x.clone(),
                        });
                    }
                }
                if let Some(deps) = deps {
                    rstmp = arena.alloc(Mult(
                        rstmp,
                        atom(r.clone(), term_ref!(fun z(), deps), arena),
                    ));
                }
                result = arena.alloc(Plus(result, rstmp));
            }
            result
        } else {
            let f = increase_foreign_vars(f, 0);
            let f = app_ref!(f, term_ref!(v 0));
            let f = term_ref!(fun z(), f);
            phase2(r, f, arena)
        }
    }
    if l != term_ref!(n 0) {
        return arena.alloc(minus(
            sigma_to_arith(term_ref!(n 0), r, f.clone(), arena),
            sigma_to_arith(term_ref!(n 0), l, f, arena),
            arena,
        ));
    }
    let rp = Poly::from(r);
    let rpc = rp.constant();
    if *rpc > 5i32.into() || *rpc < (-5i32).into() {
        return phase2(rp.into_term(), f, arena);
    }
    let rpc: i32 = rpc.try_into().unwrap();
    let mut t = if rp.variables().is_empty() {
        arena.alloc(Const(0.into()))
    } else {
        phase2(rp.with_constant(0).into_term(), f.clone(), arena)
    };
    for i in 0..rpc {
        let f_i = brain::normalize(app_ref!(f, rp.with_constant(i).into_term()));
        t = arena.alloc(Plus(t, term_ref_to_arith(f_i, arena)));
    }
    for i in rpc..0 {
        let f_i = brain::normalize(app_ref!(f, rp.with_constant(i).into_term()));
        t = arena.alloc(minus(t, term_ref_to_arith(f_i, arena), arena));
    }
    t
}

fn atom_normalizer(t: TermRef) -> ArithTree<'static> {
    fn f(t: TermRef) -> TermRef {
        match t.as_ref() {
            Term::App { func, op } => {
                let op = if type_of(op.clone()) == Ok(z()) {
                    Poly::from(op.clone()).into_term()
                } else {
                    f(op.clone())
                };
                let func = f(func.clone());
                app_ref!(func, op)
            }
            _ => t,
        }
    }
    Atom(f(t))
}

fn term_ref_to_arith(t: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
    let arith_tree = match t.as_ref() {
        Term::App { func, op: op2 } => match func.as_ref() {
            Term::App { func, op: op1 } => match func.as_ref() {
                Term::App { func, op } => match func.as_ref() {
                    Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                        "sigma" => {
                            return sigma_to_arith(op.clone(), op1.clone(), op2.clone(), arena);
                        }
                        "cnt" => {
                            return cnt_to_arith(op.clone(), op1.clone(), op2.clone(), arena);
                        }
                        _ => atom_normalizer(t),
                    },
                    _ => atom_normalizer(t),
                },
                Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                    "plus" => Plus(
                        term_ref_to_arith(op1.clone(), arena),
                        term_ref_to_arith(op2.clone(), arena),
                    ),
                    "minus" => minus(
                        term_ref_to_arith(op1.clone(), arena),
                        term_ref_to_arith(op2.clone(), arena),
                        arena,
                    ),
                    "pow" => pow_to_arith(op1.clone(), op2.clone(), arena),
                    "mult" => Mult(
                        term_ref_to_arith(op1.clone(), arena),
                        term_ref_to_arith(op2.clone(), arena),
                    ),
                    "len1" => return len1_to_arith(op1.clone(), op2.clone(), arena),
                    _ => atom_normalizer(t),
                },
                _ => atom_normalizer(t),
            },
            _ => atom_normalizer(t),
        },
        Term::Number { value } => Const(value.clone()),
        _ => atom_normalizer(t),
    };
    arena.alloc(arith_tree)
}

fn minus<'a>(
    op1: &'a ArithTree<'a>,
    op2: &'a ArithTree<'a>,
    arena: ArithArena<'a>,
) -> ArithTree<'a> {
    Plus(op1, arena.alloc(Mult(arena.alloc(Const((-1).into())), op2)))
}

fn sorter(x: Poly) -> Poly {
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
            k += k2;
        } else {
            ins(k, x);
            k = k2;
            x = x2;
        }
    }
    ins(k, x);
    Poly(c, ss)
}

fn canonical<'a>(x: &'a ArithTree<'a>, arena: ArithArena<'a>) -> Poly {
    let x = normalize(x, arena);
    let x = tree_to_d2(x);
    sorter(x)
}

impl From<TermRef> for Poly {
    fn from(t: TermRef) -> Self {
        let arena = &Arena::new();
        let a = term_ref_to_arith(t, arena);
        canonical(a, arena)
    }
}

impl Poly {
    fn into_term(self) -> TermRef {
        let mut t = term_ref!(n self.0);
        for (c, zz) in self.1 {
            let mut tx = term_ref!(n c);
            for z in zz {
                tx = app_ref!(mult(), tx, z);
            }
            t = app_ref!(plus(), t, tx);
        }
        t
    }

    pub fn from_subtract(t1: TermRef, t2: TermRef) -> Self {
        let arena = &Arena::with_capacity(32);
        let a1 = term_ref_to_arith(t1, arena);
        let a2 = term_ref_to_arith(t2, arena);
        let m1 = &Const((-1).into());
        let neg_a2 = &Mult(m1, a2);
        let a = &Plus(a1, neg_a2);
        canonical(a, arena)
    }

    pub fn constant(&self) -> &BigInt {
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

    pub fn variables(&self) -> &[(BigInt, Vec<TermRef>)] {
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

    pub fn add(&mut self, num: BigInt) {
        self.0 += num;
    }
}
