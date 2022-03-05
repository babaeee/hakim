use std::collections::HashMap;
use std::fmt::Debug;

use crate::{brain::Term, TermRef};
use num_bigint::BigInt;
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
        Plus(t1, t2) => {
            let Poly(c1, r1) = tree_to_d2(*t1);
            let Poly(c2, r2) = tree_to_d2(*t2);
            Poly(c1 + c2, [r1, r2].concat())
        }
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
            Poly(0.into(), vec![(c1 * c2, [r1, r2].concat())])
        }
    }
}

fn term_ref_to_arith(t: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
    let arith_tree = match t.as_ref() {
        Term::App { func, op: op2 } => match func.as_ref() {
            Term::App { func, op: op1 } => match func.as_ref() {
                Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                    "plus" => Plus(
                        term_ref_to_arith(op1.clone(), arena),
                        term_ref_to_arith(op2.clone(), arena),
                    ),
                    "minus" => Plus(
                        term_ref_to_arith(op1.clone(), arena),
                        term_ref_to_arith(op2.clone(), arena),
                    ),
                    "mult" => Mult(
                        term_ref_to_arith(op1.clone(), arena),
                        term_ref_to_arith(op2.clone(), arena),
                    ),
                    _ => Atom(t),
                },
                _ => Atom(t),
            },
            _ => Atom(t),
        },
        Term::Number { value } => Const(value.clone()),
        _ => Atom(t),
    };
    arena.alloc(arith_tree)
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

impl Poly {
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
