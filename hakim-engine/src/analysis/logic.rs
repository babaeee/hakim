use std::cell::Cell;
use std::fmt::Debug;

use typed_arena::Arena;

use crate::{
    app_ref,
    brain::{
        definitely_inequal, detect::detect_pair, normalize, remove_unused_var, Abstraction, Term,
        TermRef,
    },
    interactive::{self, Frame},
    library::prelude::eq,
};

#[derive(Debug, Clone)]
pub enum LogicTree<'a, T> {
    Atom(T),
    Unknown,
    And(&'a LogicTree<'a, T>, &'a LogicTree<'a, T>),
    Or(&'a LogicTree<'a, T>, &'a LogicTree<'a, T>),
    Not(&'a LogicTree<'a, T>),
}
use LogicTree::*;

#[derive(Debug, Clone)]
pub enum LogicValue<'a, T> {
    Exp(LogicTree<'a, T>),
    True,
    False,
}

mod logic_value_impls {
    use super::{
        LogicArena, LogicTree,
        LogicValue::{self, *},
    };

    impl<'a, T> From<T> for LogicValue<'a, T> {
        fn from(v: T) -> Self {
            Exp(LogicTree::Atom(v))
        }
    }

    impl<'a, T> LogicValue<'a, T> {
        pub fn not(self, arena: LogicArena<'a, T>) -> Self {
            match self {
                Exp(x) => Exp(LogicTree::Not(arena.alloc(x))),
                True => False,
                False => True,
            }
        }

        pub fn or(self, other: Self, arena: LogicArena<'a, T>) -> Self {
            match (self, other) {
                (Exp(a), Exp(b)) => {
                    let a = arena.alloc(a);
                    let b = arena.alloc(b);
                    Exp(LogicTree::Or(a, b))
                }
                (True, _) | (_, True) => True,
                (False, x) | (x, False) => x,
            }
        }

        pub fn and(self, other: Self, arena: LogicArena<'a, T>) -> Self {
            match (self, other) {
                (Exp(a), Exp(b)) => {
                    let a = arena.alloc(a);
                    let b = arena.alloc(b);
                    Exp(LogicTree::And(a, b))
                }
                (False, _) | (_, False) => False,
                (True, x) | (x, True) => x,
            }
        }

        pub fn unknown() -> Self {
            Self::Exp(LogicTree::Unknown)
        }
    }

    impl<'a, T> Default for LogicValue<'a, T> {
        fn default() -> Self {
            Self::unknown()
        }
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
            And(..) => add(&self.ahyps),
            Or(..) => add(&self.bhyps),
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
    root: Cell<LogicValue<'a, T>>,
    f: fn(t: TermRef, arena: LogicArena<'a, T>) -> LogicValue<'a, T>,
}

impl<T: Clone + Debug> LogicBuilder<'_, T> {
    pub fn build_tactic(
        name: &'static str,
        frame: Frame,
        convert: for<'a> fn(t: TermRef, arena: LogicArena<'a, T>) -> LogicValue<'a, T>,
        check_contradiction: fn(&[T]) -> bool,
        negator: fn(T) -> T,
    ) -> interactive::tactic::Result<Vec<Frame>> {
        use interactive::tactic::Error::*;
        let logic_builder = LogicBuilder::new(convert);
        logic_builder.and_not_term(normalize(frame.goal));
        for hyp in frame.hyps {
            logic_builder.and_term(normalize(hyp.ty));
        }
        if logic_builder.check_contradiction(check_contradiction, negator) {
            Ok(vec![])
        } else {
            Err(CanNotSolve(name))
        }
    }
}

impl<'a, T: Clone + Debug> LogicBuilder<'a, T> {
    pub fn new(f: fn(t: TermRef, arena: LogicArena<'a, T>) -> LogicValue<'a, T>) -> Self {
        let arena = Arena::new();
        Self {
            arena,
            hyps: Hyps::new(),
            root: Cell::new(LogicValue::unknown()),
            f,
        }
    }

    fn and(&'a self, item: LogicValue<'a, T>) {
        let old_root = self.root.take();
        self.root.set(old_root.and(item, &self.arena));
    }

    pub fn and_term(&'a self, term: TermRef) {
        let item = self.convert_term(term);
        self.and(item);
    }

    pub fn and_not_term(&'a self, term: TermRef) {
        let item = self.convert_term(term);
        let not = item.not(&self.arena);
        self.and(not);
    }

    fn convert_term(&'a self, term: TermRef) -> LogicValue<'a, T> {
        if let Term::Forall(Abstraction {
            var_ty,
            body,
            hint_name: _,
        }) = term.as_ref()
        {
            if let Some(body) = remove_unused_var(body.clone()) {
                let op1 = self.convert_term(var_ty.clone());
                let op2 = self.convert_term(body);
                return op2.or(op1.not(&self.arena), &self.arena);
            }
        }
        if let Term::Axiom { unique_name, .. } = term.as_ref() {
            if unique_name == "False" || unique_name == "True" {
                return match unique_name.as_str() {
                    "True" => LogicValue::True,
                    "False" => LogicValue::False,
                    _ => unreachable!(),
                };
            }
        }
        if let Term::App { func, op: op2 } = term.as_ref() {
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "and" || unique_name == "or" {
                        let op1 = self.convert_term(op1.clone());
                        let op2 = self.convert_term(op2.clone());
                        return match unique_name.as_str() {
                            "and" => op1.and(op2, &self.arena),
                            "or" => op1.or(op2, &self.arena),
                            _ => unreachable!(),
                        };
                    }
                }
                if let Term::App { func, op: _ } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        if unique_name == "eq" {
                            if definitely_inequal(op1, op2) {
                                return LogicValue::False;
                            }
                            if let Some((a, b, ty1, ty2)) = detect_pair(op1) {
                                if let Some((c, d, _, _)) = detect_pair(op2) {
                                    let x1 = self.convert_term(app_ref!(eq(), ty1, a, c));
                                    let x2 = self.convert_term(app_ref!(eq(), ty2, b, d));
                                    return x1.and(x2, &self.arena);
                                }
                            }
                        }
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
        let root = self.root.take();
        let root = match root {
            LogicValue::Exp(e) => self.arena.alloc(e),
            LogicValue::True => return false,
            LogicValue::False => return true,
        };
        self.hyps.add_hyp(root, false, negator);
        self.dfs(checker, negator)
    }
}
