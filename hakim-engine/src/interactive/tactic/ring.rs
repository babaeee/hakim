use super::{rewrite::get_eq_params, Error::*, Result};
use crate::{brain::Term, interactive::Frame, TermRef};
use typed_arena::Arena;

#[derive(Debug, Clone)]
enum ArithTree<'a> {
    Atom(TermRef),
    Const(BigInt),
    Plus(&'a ArithTree<'a>, &'a ArithTree<'a>),
    Mult(&'a ArithTree<'a>, &'a ArithTree<'a>),
}

use num_bigint::BigInt;
use ArithTree::*;

type Poly = (BigInt, Vec<(BigInt, Vec<TermRef>)>);
type ArithArena<'a> = &'a Arena<ArithTree<'a>>;

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
        Atom(t) => (0.into(), vec![(1.into(), vec![t.clone()])]),
        Const(i) => (i.clone(), vec![]),
        Plus(t1, t2) => {
            let (c1, r1) = tree_to_d2(*t1);
            let (c2, r2) = tree_to_d2(*t2);
            (c1 + c2, [r1, r2].concat())
        }
        Mult(t1, t2) => {
            fn to_mul(x: &ArithTree<'_>) -> (BigInt, Vec<TermRef>) {
                let (c1, mut r1) = tree_to_d2(x);
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
            (0.into(), vec![(c1 * c2, [r1, r2].concat())])
        }
    }
}

fn term_ref_to_arith(t: TermRef, arena: ArithArena<'_>) -> &ArithTree<'_> {
    let arith_tree = match t.as_ref() {
        Term::App { func, op: op2 } => match func.as_ref() {
            Term::App { func, op: op1 } => match func.as_ref() {
                Term::Axiom { unique_name, .. } => {
                    if unique_name == "plus" {
                        Plus(
                            term_ref_to_arith(op1.clone(), arena),
                            term_ref_to_arith(op2.clone(), arena),
                        )
                    } else if unique_name == "mult" {
                        Mult(
                            term_ref_to_arith(op1.clone(), arena),
                            term_ref_to_arith(op2.clone(), arena),
                        )
                    } else {
                        Atom(t)
                    }
                }
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

fn canonical<'a>(x: &'a ArithTree<'a>, arena: ArithArena<'a>) -> Poly {
    let x = normalize(x, arena);
    let x = tree_to_d2(x);

    sorter(x)
}

pub fn ring(frame: Frame) -> Result<Vec<Frame>> {
    let goal = frame.goal;
    let [op1, op2, _] = get_eq_params(&goal).ok_or(BadGoal("ring only work on equality"))?;
    let arena = &Arena::with_capacity(32);
    let d1 = canonical(term_ref_to_arith(op1, arena), arena);
    let d2 = canonical(term_ref_to_arith(op2, arena), arena);
    if d1 == d2 {
        Ok(vec![])
    } else {
        Err(CanNotSolve("ring"))
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn success_ring1() {
        run_interactive_to_end(
            "forall x: ℤ, eq ℤ (x + x) (2 * x)",
            r#"
        intros x
        ring
        "#,
        );
    }

    #[test]
    fn success_ring2() {
        run_interactive_to_end(
            "forall a b: ℤ, eq ℤ (mult (plus a b) (plus a b)) \
        (plus (mult a a) (plus (mult 2 (mult a b)) (mult b b)))",
            r#"
        intros a
        intros b
        ring
        "#,
        );
    }
}
