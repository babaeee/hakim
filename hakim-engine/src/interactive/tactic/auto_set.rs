use super::{Error::*, Result};
use crate::{
    analysis::logic::{LogicArena, LogicBuilder, LogicTree},
    app_ref,
    brain::{Term, TermRef},
    interactive::Frame,
    library::prelude::set,
    term_ref,
};
use typed_arena::Arena;

#[derive(Debug, Clone)]
enum EnsembleTree<'a> {
    Set(TermRef),
    Union(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Intersection(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Setminus(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Eq(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Included(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Inset(TermRef, &'a EnsembleTree<'a>),
    Outset(TermRef, &'a EnsembleTree<'a>),
}
use EnsembleTree::*;

type EnsembleArena<'a> = &'a Arena<EnsembleTree<'a>>;

#[derive(Debug, Clone)]
enum EnsembleStatement {
    IsMember(TermRef, TermRef),
    IsNotMember(TermRef, TermRef),
    IsSubset(TermRef, TermRef),
    IsNotSubset(TermRef, TermRef),
}

use std::collections::HashMap;
struct Identifier {
    map: HashMap<TermRef, usize>,
    id_counter: usize,
}
impl Identifier {
    pub fn new() -> Identifier {
        Identifier {
            map: HashMap::new(),
            id_counter: 1,
        }
    }
    pub fn get(&mut self, v: &TermRef) -> usize {
        match self.map.get(v) {
            Some(&x) => x,
            None => {
                self.map.insert(v.clone(), self.id_counter);
                self.id_counter += 1;
                self.id_counter - 1
            }
        }
    }
}

fn from_set_type<'a>(
    t: &TermRef,
    arena: EnsembleArena<'a>,
    sets_id: &mut Identifier,
) -> &'a EnsembleTree<'a> {
    if let Term::App { func, op: op2 } = t.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: _ } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "union" {
                        let set_a = from_set_type(op1, arena, sets_id);
                        let set_b = from_set_type(op2, arena, sets_id);
                        return arena.alloc(Union(set_a, set_b));
                    }
                    if unique_name == "intersection" {
                        let set_a = from_set_type(op1, arena, sets_id);
                        let set_b = from_set_type(op2, arena, sets_id);
                        return arena.alloc(Intersection(set_a, set_b));
                    }
                    if unique_name == "setminus" {
                        let set_a = from_set_type(op1, arena, sets_id);
                        let set_b = from_set_type(op2, arena, sets_id);
                        return arena.alloc(Setminus(set_a, set_b));
                    }
                }
            }
        }
    }
    return arena.alloc(Set(t.clone()));
}
fn from_prop_type<'a>(
    t: TermRef,
    arena: EnsembleArena<'a>,
    elements_id: &mut Identifier,
    sets_id: &mut Identifier,
) -> Option<(&'a EnsembleTree<'a>, TermRef)> {
    if let Term::Forall(a) = t.as_ref() {
        if let Term::Axiom { unique_name, .. } = a.body.as_ref() {
            if unique_name == "False" {
                if let Some((Inset(x, set_a), ty)) =
                    from_prop_type(a.var_ty.clone(), arena, elements_id, sets_id)
                {
                    return Some((arena.alloc(Outset(x.clone(), set_a)), ty));
                }
            }
            //the Included -> false or eq -> false type prop is one work
        }
    }

    if let Term::App { func, op: op2 } = t.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "inset" {
                        let tree = Inset(op1.clone(), from_set_type(op2, arena, sets_id));
                        return Some((arena.alloc(tree), term_ref!(app_ref!(set(), ty))));
                    }
                    if unique_name == "included" {
                        let tree = Included(
                            from_set_type(op1, arena, sets_id),
                            from_set_type(op2, arena, sets_id),
                        );
                        return Some((arena.alloc(tree), term_ref!(app_ref!(set(), ty))));
                    }
                    if unique_name == "eq" {
                        let tree = Eq(
                            from_set_type(op1, arena, sets_id),
                            from_set_type(op2, arena, sets_id),
                        );
                        return Some((arena.alloc(tree), ty.clone()));
                    }
                }
            }
        }
    }
    None
}

fn convert(
    term: TermRef,
    logic_arena: LogicArena<'_, EnsembleStatement>,
) -> &LogicTree<'_, EnsembleStatement> {
    let my_arena = Arena::new();
    let exp = if let Some(x) = from_prop_type(
        term,
        &my_arena,
        &mut Identifier::new(),
        &mut Identifier::new(),
    ) {
        x.0
    } else {
        return logic_arena.alloc(LogicTree::Unknown);
    };
    fn f<'a>(
        exp: &EnsembleTree<'_>,
        arena: LogicArena<'a, EnsembleStatement>,
    ) -> &'a LogicTree<'a, EnsembleStatement> {
        match exp {
            Set(_) => unreachable!(),
            Union(_, _) => unreachable!(),
            Intersection(_, _) => unreachable!(),
            Setminus(_, _) => unreachable!(),
            Eq(x, y) => {
                let l = f(&Included(x, y), arena);
                let r = f(&Included(y, x), arena);
                arena.alloc(LogicTree::And(l, r))
            }
            Included(_, Union(..) | Setminus(..))
            | Included(Intersection(..) | Setminus(..), _) => {
                arena.alloc(LogicTree::Unknown) // TODO: what to do?
            }
            Included(x, Intersection(a, b)) => {
                let l = f(&Included(x, a), arena);
                let r = f(&Included(x, b), arena);
                arena.alloc(LogicTree::And(l, r))
            }
            Included(Union(a, b), x) => {
                let l = f(&Included(a, x), arena);
                let r = f(&Included(b, x), arena);
                arena.alloc(LogicTree::And(l, r))
            }
            Included(Set(a), Set(b)) => arena.alloc(LogicTree::Atom(EnsembleStatement::IsSubset(
                a.clone(),
                b.clone(),
            ))),
            Included(..) => unreachable!(),
            Inset(x, Union(a, b)) => {
                let l = f(&Inset(x.clone(), a), arena);
                let r = f(&Inset(x.clone(), b), arena);
                arena.alloc(LogicTree::Or(l, r))
            }
            Inset(x, Intersection(a, b)) => {
                let l = f(&Inset(x.clone(), a), arena);
                let r = f(&Inset(x.clone(), b), arena);
                arena.alloc(LogicTree::And(l, r))
            }
            Inset(x, Setminus(a, b)) => {
                let l = f(&Inset(x.clone(), a), arena);
                let r = f(&Inset(x.clone(), b), arena);
                let r = arena.alloc(LogicTree::Not(r));
                arena.alloc(LogicTree::And(l, r))
            }
            Inset(x, Set(a)) => arena.alloc(LogicTree::Atom(EnsembleStatement::IsMember(
                x.clone(),
                a.clone(),
            ))),
            Inset(..) => unreachable!(),
            Outset(_, _) => todo!(),
        }
    }
    dbg!(f(exp, logic_arena))
}

enum InternedStatement {
    IsMember(usize, usize),
    IsNotMember(usize, usize),
    IsSubset(usize, usize),
    IsNotSubset(usize, usize),
}

impl InternedStatement {
    fn intern_array(a: &[EnsembleStatement]) -> Vec<Self> {
        let mut interner = Identifier::new();
        a.iter()
            .map(|x| match x {
                EnsembleStatement::IsMember(a, b) => {
                    let a = interner.get(a);
                    let b = interner.get(b);
                    Self::IsMember(a, b)
                }
                EnsembleStatement::IsNotMember(a, b) => {
                    let a = interner.get(a);
                    let b = interner.get(b);
                    Self::IsNotMember(a, b)
                }
                EnsembleStatement::IsSubset(a, b) => {
                    let a = interner.get(a);
                    let b = interner.get(b);
                    Self::IsSubset(a, b)
                }
                EnsembleStatement::IsNotSubset(a, b) => {
                    let a = interner.get(a);
                    let b = interner.get(b);
                    Self::IsNotSubset(a, b)
                }
            })
            .collect()
    }
}

fn check_contradiction(a: &[EnsembleStatement]) -> bool {
    use InternedStatement::*;
    let a = InternedStatement::intern_array(a);
    let cnt_vars = a
        .iter()
        .map(|x| match x {
            IsMember(a, b) | IsNotMember(a, b) | IsSubset(a, b) | IsNotSubset(a, b) => {
                std::cmp::max(*a, *b)
            }
        })
        .max();
    let mut cnt_vars = if let Some(x) = cnt_vars {
        x
    } else {
        return false;
    };
    let mut m = HashMap::<(usize, usize), bool>::new();
    let mut edges = vec![vec![]; cnt_vars];
    for x in &a {
        match x {
            IsMember(a, b) => {
                if m.get(&(*a, *b)) == Some(&false) {
                    return true;
                }
                m.insert((*a, *b), true);
            }
            IsNotMember(a, b) => {
                if m.get(&(*a, *b)) == Some(&true) {
                    return true;
                }
                m.insert((*a, *b), false);
            }
            IsSubset(a, b) => {
                edges[*a].push(*b);
            }
            IsNotSubset(a, b) => {
                let new_var = cnt_vars;
                cnt_vars += 1;
                m.insert((new_var, *a), true);
                m.insert((new_var, *b), false);
            }
        }
    }
    for _ in 0..cnt_vars {
        let it = m.clone().into_iter();
        for ((a, b), v) in it {
            if v {
                for c in &edges[b] {
                    if m.get(&(a, *c)) == Some(&false) {
                        return true;
                    }
                    m.insert((a, *c), true);
                }
            }
        }
    }
    false
}

fn negator(x: EnsembleStatement) -> EnsembleStatement {
    match x {
        EnsembleStatement::IsMember(a, b) => EnsembleStatement::IsNotMember(a, b),
        EnsembleStatement::IsNotMember(a, b) => EnsembleStatement::IsMember(a, b),
        EnsembleStatement::IsSubset(a, b) => EnsembleStatement::IsNotSubset(a, b),
        EnsembleStatement::IsNotSubset(a, b) => EnsembleStatement::IsSubset(a, b),
    }
}

pub fn auto_set(frame: Frame) -> Result<Vec<Frame>> {
    let logic_builder = LogicBuilder::new(convert);
    logic_builder.and_not_term(frame.goal);
    for (_, hyp) in frame.hyps {
        logic_builder.and_term(hyp);
    }
    if logic_builder.check_contradiction(check_contradiction, negator) {
        Ok(vec![])
    } else {
        Err(CanNotSolve("auto_set"))
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nauto_set");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "auto_set");
    }

    #[test]
    fn success1() {
        success("∀ T: U, ∀ a: T, ∀ A B C: set T, a ∈ C ∩ B -> a ∈ A ∩ C -> a ∈ C ∩ B ∩ A");
    }

    #[test]
    fn subset_trans() {
        success("∀ T: U, ∀ A B C: set T, A ⊆ B → B ⊆ C → A ⊆ C");
    }

    #[test]
    fn union() {
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∪ B → a ∈ A ∨ a ∈ B");
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∨ a ∈ B → a ∈ A ∪ B");
    }

    #[test]
    fn intersect() {
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∩ B → a ∈ A");
        fail("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A → a ∈ A ∩ B");
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∩ B → a ∈ B");
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∧ a ∈ B → a ∈ A ∩ B");
        success("∀ T: U, ∀ A B C: set T, A ⊆ C ∩ B -> A ⊆ C");
    }

    #[test]
    #[ignore]
    fn success2() {
        success("∀ T: U, ∀ a: T, ∀ A B C D E F: set T, a ∈ C -> a ∈ E -> a ∈ (A ∪ (B ∪ C)) ∩ (D ∪ (E ∩ F))");
    }
}
