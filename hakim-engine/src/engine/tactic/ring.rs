use super::{rewrite::get_eq_params, Error::*, Result};
use crate::{brain::Term, engine::interactive::Frame, TermRef};

#[derive(Debug, Clone)]
enum ArithTree {
    Atom(TermRef),
    Const(i32),
    Plus(Box<ArithTree>, Box<ArithTree>),
    Mult(Box<ArithTree>, Box<ArithTree>),
}

use ArithTree::*;

type Poly = (i32, Vec<(i32, Vec<TermRef>)>);

fn normalize(tree: ArithTree) -> ArithTree {
    match tree {
        Atom(_) | Const(_) => tree,
        Plus(a, b) => Plus(Box::new(normalize(*a)), Box::new(normalize(*b))),
        Mult(a, b) => {
            let a = normalize(*a);
            let b = normalize(*b);
            if let Plus(x, y) = a {
                let xb = normalize(Mult(x, Box::new(b.clone())));
                let yb = normalize(Mult(y, Box::new(b.clone())));
                return Plus(Box::new(xb), Box::new(yb));
            }
            if let Plus(x, y) = b {
                let xa = normalize(Mult(x, Box::new(a.clone())));
                let ya = normalize(Mult(y, Box::new(a.clone())));
                return Plus(Box::new(xa), Box::new(ya));
            }
            return Mult(Box::new(a), Box::new(b));
        }
    }
}

fn tree_to_d2(tree: ArithTree) -> Poly {
    match tree {
        Atom(t) => (0, vec![(1, vec![t.clone()])]),
        Const(i) => (i, vec![]),
        Plus(t1, t2) => {
            let (c1, r1) = tree_to_d2(*t1);
            let (c2, r2) = tree_to_d2(*t2);
            (c1 + c2, [r1, r2].concat())
        }
        Mult(t1, t2) => {
            fn to_mul(x: ArithTree) -> (i32, Vec<TermRef>) {
                let (c1, mut r1) = tree_to_d2(x);
                if r1.is_empty() {
                    return (c1, vec![]);
                }
                if r1.len() != 1 || c1 != 0 {
                    panic!("tree is not normalized. this is a bug");
                }
                r1.pop().unwrap()
            }
            let (c1, r1) = to_mul(*t1);
            let (c2, r2) = to_mul(*t2);
            (0, vec![(c1 * c2, [r1, r2].concat())])
        }
    }
}

impl From<TermRef> for ArithTree {
    fn from(t: TermRef) -> Self {
        match t.as_ref() {
            Term::App { func, op: op2 } => match func.as_ref() {
                Term::App { func, op: op1 } => match func.as_ref() {
                    Term::Axiom { unique_name, .. } => {
                        if unique_name == "plus" {
                            Plus(Box::new(op1.clone().into()), Box::new(op2.clone().into()))
                        } else if unique_name == "mult" {
                            Mult(Box::new(op1.clone().into()), Box::new(op2.clone().into()))
                        } else {
                            Atom(t)
                        }
                    }
                    _ => Atom(t),
                },
                _ => Atom(t),
            },
            Term::Number { value } => Const(*value),
            _ => Atom(t),
        }
    }
}

fn sorter(x: Poly) -> Poly {
    let (c, mut v) = x;
    for e in &mut v {
        e.1.sort();
    }
    v.sort_by(|a, b| a.1.cmp(&b.1));
    let mut ss = vec![];
    let mut iter = v.into_iter();
    let (mut k, mut x) = match iter.next() {
        Some(f) => f,
        None => return (c, vec![]),
    };
    for (k2, x2) in iter {
        if x == x2 {
            k += k2;
        } else {
            ss.push((k, x));
            k = k2;
            x = x2;
        }
    }
    ss.push((k, x));
    (c, ss)
}

fn canonical(x: ArithTree) -> Poly {
    let x = normalize(x);
    let x = tree_to_d2(x);
    let x = sorter(x);
    x
}

pub fn ring(frame: Frame) -> Result<Vec<Frame>> {
    let goal = frame.goal.clone();
    let [op1, op2] =
        get_eq_params(&frame.engine, goal).ok_or(BadGoal("ring only work on equality"))?;
    let d1 = canonical(ArithTree::from(op1));
    let d2 = canonical(ArithTree::from(op2));
    if d1 == d2 {
        Ok(vec![])
    } else {
        Err(CanNotSolve("ring"))
    }
}
