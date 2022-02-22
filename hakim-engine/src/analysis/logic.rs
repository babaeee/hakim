use std::cell::Cell;

use typed_arena::Arena;

use crate::brain::{Term, TermRef};

#[derive(Debug, Clone)]
pub enum LogicTree<'a, T> {
    Atom(T),
    Unknown,
    And(&'a LogicTree<'a, T>, &'a LogicTree<'a, T>),
    Or(&'a LogicTree<'a, T>, &'a LogicTree<'a, T>),
    Not(&'a LogicTree<'a, T>),
}
use LogicTree::*;

impl<'a, T> Default for LogicTree<'a, T> {
    fn default() -> Self {
        Unknown
    }
}

pub type LogicArena<'a, T> = &'a Arena<LogicTree<'a, T>>;

pub struct LogicBuilder<'a, T> {
    arena: Arena<LogicTree<'a, T>>,
    root: Cell<LogicTree<'a, T>>,
    f: fn(t: TermRef, arena: LogicArena<'a, T>) -> &'a LogicTree<'a, T>,
}

fn logic_to_vec<T: Clone>(tree: &LogicTree<'_, T>, negator: fn(T) -> T) -> Vec<T> {
    fn f<T: Clone>(tree: &LogicTree<'_, T>, negator: fn(T) -> T, r: &mut Vec<T>) {
        match tree {
            Atom(t) => r.push(t.clone()),
            Unknown => (),
            And(x, y) => {
                f(x, negator, r);
                f(y, negator, r);
            }
            Or(_, _) => todo!(),
            Not(Atom(t)) => r.push(negator(t.clone())),
            Not(Unknown) => (),
            Not(_) => todo!(),
        }
    }
    let mut r = vec![];
    f(tree, negator, &mut r);
    r
}

impl<'a, T: Clone> LogicBuilder<'a, T> {
    pub fn new(f: fn(t: TermRef, arena: LogicArena<'a, T>) -> &'a LogicTree<'a, T>) -> Self {
        let arena = Arena::new();
        Self {
            arena,
            root: Cell::new(Unknown),
            f,
        }
    }

    fn and(&'a self, item: &'a LogicTree<'a, T>) {
        let old_root = self.arena.alloc(self.root.take());
        self.root.set(And(old_root, item));
    }

    pub fn and_term(&'a self, term: TermRef) {
        let item = self.convert_term(term);
        self.and(item);
    }

    pub fn and_not_term(&'a self, term: TermRef) {
        let item = self.convert_term(term);
        let not = self.arena.alloc(Not(item));
        self.and(not);
    }

    fn convert_term(&'a self, term: TermRef) -> &'a LogicTree<'a, T> {
        if let Term::App { func, op: op2 } = term.as_ref() {
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "and" || unique_name == "or" {
                        let op1 = self.convert_term(op1.clone());
                        let op2 = self.convert_term(op2.clone());
                        return match unique_name.as_str() {
                            "and" => self.arena.alloc(And(op1, op2)),
                            "or" => self.arena.alloc(Or(op1, op2)),
                            _ => unreachable!(),
                        };
                    }
                }
            }
        }
        (self.f)(term, &self.arena)
    }

    pub fn check_contradiction(&'a self, checker: fn(&[T]) -> bool, negator: fn(T) -> T) -> bool {
        let root = self.root.take();
        let vec = logic_to_vec(&root, negator);
        checker(&vec)
    }
}
