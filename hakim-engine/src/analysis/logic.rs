use std::cell::Cell;
use std::fmt::Debug;

use typed_arena::Arena;

use crate::brain::{remove_unused_var, Abstraction, Term, TermRef};

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

struct CellVec<T>(Cell<Vec<T>>);

impl<T> From<Vec<T>> for CellVec<T> {
    fn from(x: Vec<T>) -> Self {
        CellVec(Cell::new(x))
    }
}

impl<T> CellVec<T> {
    fn pop(&self) -> Option<T> {
        let mut x = self.0.take();
        let r = x.pop();
        self.0.set(x);
        r
    }

    fn push(&self, v: T) {
        let mut x = self.0.take();
        x.push(v);
        self.0.set(x);
    }
}

struct Hyps<'a, T> {
    simple_hyps: CellVec<T>,
    ahyps: CellVec<&'a LogicTree<'a, T>>,
    bhyps: CellVec<&'a LogicTree<'a, T>>,
}
impl<'a, T: Clone + Debug> Hyps<'a, T> {
    pub fn new() -> Hyps<'a, T> {
        let simple_hyps: CellVec<T> = Vec::new().into();
        //hypothis that generate two goal
        let bhyps: CellVec<&LogicTree<T>> = Vec::new().into();
        //hyps that not
        let ahyps: CellVec<&LogicTree<T>> = Vec::new().into();
        Hyps {
            simple_hyps,
            ahyps,
            bhyps,
        }
    }
    fn add_hyp(&self, h: &'a LogicTree<'a, T>, undo: bool, negator: fn(T) -> T) {
        let add = |hyps: &CellVec<&LogicTree<'a, T>>| {
            if undo {
                hyps.pop();
            } else {
                //                dbg!(h);
                hyps.push(h);
            }
        };
        match h {
            And(x, y) => {
                if let Unknown = x {
                    self.add_hyp(y, undo, negator);
                } else if let Unknown = y {
                    self.add_hyp(x, undo, negator);
                } else {
                    add(&self.ahyps);
                }
            }
            Or(x, y) => {
                if let Unknown = x {
                    self.add_hyp(y, undo, negator);
                } else if let Unknown = y {
                    self.add_hyp(x, undo, negator);
                } else {
                    add(&self.bhyps);
                }
            }
            Not(x) => match x {
                Or(..) => add(&self.ahyps),
                And(..) => add(&self.bhyps),
                Atom(t) => {
                    if undo {
                        self.simple_hyps.pop();
                    } else {
                        self.simple_hyps.push(negator(t.clone()));
                    }
                }
                Not(x) => self.add_hyp(x, undo, negator),
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
    hyps: Hyps<'a, T>,
    root: Cell<LogicTree<'a, T>>,
    f: fn(t: TermRef, arena: LogicArena<'a, T>) -> &'a LogicTree<'a, T>,
}
impl<'a, T: Clone + Debug> LogicBuilder<'a, T> {
    pub fn new(f: fn(t: TermRef, arena: LogicArena<'a, T>) -> &'a LogicTree<'a, T>) -> Self {
        let arena = Arena::new();
        Self {
            arena,
            hyps: Hyps::new(),
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
        if let Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) = term.as_ref()
        {
            if let Some(body) = remove_unused_var(body.clone(), 0) {
                let op1 = self.convert_term(var_ty.clone());
                let op2 = self.convert_term(body);
                let op1 = self.arena.alloc(Not(op1));
                return self.arena.alloc(Or(op1, op2));
            }
        }
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
    fn dfs(&'a self, checker: fn(&[T]) -> bool, negator: fn(T) -> T) -> bool {
        /*        println!("bhyps");
                let tmp = self.hyps.bhyps.0.take();
                for a in &tmp {
                    print!("{:?} ", a);
                }
                println!();
                self.hyps.bhyps.0.set(tmp);
        */
        let mut ans = false;
        let mut found = false;

        let step1 = |h1, h2| {
            //            dbg!("step1");
            //            dbg!("h1");
            self.hyps.add_hyp(h1, false, negator);
            //            dbg!("h2");
            self.hyps.add_hyp(h2, false, negator);
            let c = self.dfs(checker, negator);
            self.hyps.add_hyp(h2, true, negator);
            self.hyps.add_hyp(h1, true, negator);
            c
        };
        if let Some(h) = self.hyps.ahyps.pop() {
            match h {
                And(x, y) => {
                    ans = step1(x, y);
                    found = true;
                }
                Not(Atom(..)) => todo!(),
                Not(Or(x, y)) => {
                    ans = step1(self.arena.alloc(Not(x)), self.arena.alloc(Not(y)));
                    found = true;
                }
                _ => (),
            }
            self.hyps.ahyps.push(h);
        }
        if found {
            return ans;
        }

        let step2 = |h1, h2| {
            //            dbg!("step2");
            //            dbg!("h1");
            self.hyps.add_hyp(h1, false, negator);
            let mut ans = self.dfs(checker, negator);
            self.hyps.add_hyp(h1, true, negator);

            if ans {
                //                dbg!("h2");
                self.hyps.add_hyp(h2, false, negator);
                ans = self.dfs(checker, negator);
                self.hyps.add_hyp(h2, true, negator);
            }
            ans
        };
        if let Some(h) = self.hyps.bhyps.pop() {
            if let Or(x, y) = h {
                ans = step2(x, y);
                found = true;
            }
            if let Not(And(x, y)) = h {
                ans = step2(self.arena.alloc(Not(x)), self.arena.alloc(Not(y)));
                found = true;
            }
            self.hyps.bhyps.push(h);
        }
        if found {
            return ans;
        }
        let sh = self.hyps.simple_hyps.0.take();
        ans = checker(&sh);
        self.hyps.simple_hyps.0.set(sh);
        ans
    }
    pub fn check_contradiction(&'a self, checker: fn(&[T]) -> bool, negator: fn(T) -> T) -> bool {
        let root = self.arena.alloc(self.root.take());
        self.hyps.add_hyp(root, false, negator);
        self.dfs(checker, negator)
    }
}
