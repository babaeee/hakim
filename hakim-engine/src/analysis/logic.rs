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

struct Hyps<'a, T> {
    simple_hyps: Vec<T>,
    ahyps: Vec<&'a LogicTree<'a, T>>,
    bhyps: Vec<&'a LogicTree<'a, T>>,
}
impl<'a, T: Clone> Hyps<'a, T> {
    pub fn new() -> Hyps<'a, T> {
        let simple_hyps: Vec<T> = Vec::new();
        //hypothis that generate two goal
        let bhyps: Vec<&LogicTree<T>> = Vec::new();
        //hyps that not
        let ahyps: Vec<&LogicTree<T>> = Vec::new();
        Hyps {
            simple_hyps,
            ahyps,
            bhyps,
        }
    }
    fn add_hyp(&mut self, h: &'a LogicTree<'a, T>, undo: bool) {
        let add = |hyps: &mut Vec<&LogicTree<'a, T>>| {
            if undo {
                hyps.pop();
            } else {
                hyps.push(h);
            }
        };
        match h {
            And(..) => add(&mut self.ahyps),
            Or(..) => add(&mut self.bhyps),
            Not(x) => match x {
                Or(..) => add(&mut self.ahyps),
                And(..) => add(&mut self.bhyps),
                Atom(..) => todo!(),
                Not(x) => self.add_hyp(x, undo),
                Unknown => (),
            },
            Atom(t) => {
                if undo {
                    self.simple_hyps.pop();
                } else {
                    self.simple_hyps.push(t.clone());
                }
            }
            Unknown => (),
        }
    }
}

pub struct LogicBuilder<'a, T> {
    arena: Arena<LogicTree<'a, T>>,
    root: Cell<LogicTree<'a, T>>,
    f: fn(t: TermRef, arena: LogicArena<'a, T>) -> &'a LogicTree<'a, T>,
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
    fn dfs(
        &'a mut self,
        hyps: &'a mut Hyps<'a, T>,
        checker: fn(&[T]) -> bool,
        negator: fn(T) -> T,
    ) -> bool {
        let mut step1 = |h1, h2| {
            hyps.add_hyp(h1, false);
            hyps.add_hyp(h2, false);
            let c = self.dfs(hyps, checker, negator);
            hyps.add_hyp(h2, true);
            hyps.add_hyp(h1, true);
            c
        };
        if let Some(h) = hyps.ahyps.pop() {
            match h {
                And(x, y) => return step1(x, y),
                Not(Atom(..)) => todo!(),
                Not(Or(x, y)) => {
                    return step1(self.arena.alloc(Not(x)), self.arena.alloc(Not(y)));
                }
                _ => (),
            }
            hyps.ahyps.push(h);
        }
        let mut step2 = |h1, h2| {
            let mut ans = false;
            hyps.add_hyp(h1, false);
            if self.dfs(hyps, checker, negator) {
                hyps.add_hyp(h2, false);
                ans = self.dfs(hyps, checker, negator);
                hyps.add_hyp(h2, true);
            }
            hyps.add_hyp(h1, true);
            return ans;
        };
        if let Some(h) = hyps.bhyps.pop() {
            if let Or(x, y) = h {
                return step2(x, y);
            }
            if let Not(And(x, y)) = h {
                return step2(self.arena.alloc(Not(x)), self.arena.alloc(Not(y)));
            }
            hyps.bhyps.push(h);
        }
        return checker(&hyps.simple_hyps);
    }
    pub fn check_contradiction(&'a self, checker: fn(&[T]) -> bool, negator: fn(T) -> T) -> bool {
        let root = self.root.take();
        let mut hyps = Hyps::new();
        hyps.add_hyp(&root, false);
        return self.dfs(&mut hyps, checker, negator);
    }
}
