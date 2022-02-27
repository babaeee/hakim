use super::{apply::apply, intros::intros, Error::*, Result};
use crate::{
    analysis::logic::{LogicArena, LogicBuilder, LogicValue},
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
    Empty,
    Singleton(TermRef),
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
    True,
    False,
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
        if let Term::Axiom { unique_name, .. } = func.as_ref() {
            if unique_name == "set_empty" {
                return arena.alloc(EnsembleTree::Empty);
            }
        }
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "set_singleton" {
                    return arena.alloc(EnsembleTree::Singleton(op2.clone()));
                }
            }
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
) -> LogicValue<'_, EnsembleStatement> {
    let my_arena = Arena::new();
    let exp = if let Some(x) = from_prop_type(
        term,
        &my_arena,
        &mut Identifier::new(),
        &mut Identifier::new(),
    ) {
        x.0
    } else {
        return LogicValue::unknown();
    };
    fn f<'a>(
        exp: &EnsembleTree<'_>,
        arena: LogicArena<'a, EnsembleStatement>,
    ) -> LogicValue<'a, EnsembleStatement> {
        match exp {
            Empty | Singleton(_) | Set(_) | Union(_, _) | Intersection(_, _) | Setminus(_, _) => {
                unreachable!()
            }
            Eq(x, y) => {
                let l = f(&Included(x, y), arena);
                let r = f(&Included(y, x), arena);
                l.and(r, arena)
            }
            Included(Empty, _) => LogicValue::True,
            Included(Singleton(a), x) => f(&Inset(a.clone(), x), arena),
            Included(x, Intersection(a, b)) => {
                let l = f(&Included(x, a), arena);
                let r = f(&Included(x, b), arena);
                l.and(r, arena)
            }
            Included(Union(a, b), x) => {
                let l = f(&Included(a, x), arena);
                let r = f(&Included(b, x), arena);
                l.and(dbg!(r), arena)
            }
            Included(Set(a), Set(b)) => {
                LogicValue::from(EnsembleStatement::IsSubset(a.clone(), b.clone()))
            }
            Included(_, Union(..) | Setminus(..) | Empty | Singleton(_))
            | Included(Intersection(..) | Setminus(..), _) => LogicValue::unknown(),
            Included(..) => unreachable!(),
            Inset(_, Empty) => LogicValue::False,
            Inset(a, Singleton(b)) => {
                if a == b {
                    LogicValue::True
                } else {
                    // not everything is a set, but it has no problem to imagine as so, because
                    // input is type checked and there is no wrong types mixing sets and non sets
                    let l = LogicValue::from(EnsembleStatement::IsSubset(a.clone(), b.clone()));
                    let r = LogicValue::from(EnsembleStatement::IsSubset(b.clone(), a.clone()));
                    l.and(r, arena)
                }
            }
            Inset(x, Union(a, b)) => {
                let l = f(&Inset(x.clone(), a), arena);
                let r = f(&Inset(x.clone(), b), arena);
                l.or(r, arena)
            }
            Inset(x, Intersection(a, b)) => {
                let l = f(&Inset(x.clone(), a), arena);
                let r = f(&Inset(x.clone(), b), arena);
                l.and(r, arena)
            }
            Inset(x, Setminus(a, b)) => {
                let l = f(&Inset(x.clone(), a), arena);
                let r = f(&Inset(x.clone(), b), arena);
                l.and(r.not(arena), arena)
            }
            Inset(x, Set(a)) => LogicValue::from(EnsembleStatement::IsMember(x.clone(), a.clone())),
            Inset(..) => unreachable!(),
            Outset(_, _) => todo!(),
        }
    }
    f(exp, logic_arena)
}

enum InternedStatement {
    IsMember(usize, usize),
    IsNotMember(usize, usize),
    IsSubset(usize, usize),
    IsNotSubset(usize, usize),
    False,
    True,
}

impl InternedStatement {
    fn intern_array(a: &[EnsembleStatement]) -> (usize, Vec<Self>) {
        let mut interner = Identifier::new();
        let r = a
            .iter()
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
                EnsembleStatement::False => Self::False,
                EnsembleStatement::True => Self::True,
            })
            .collect();
        (interner.id_counter, r)
    }
}

fn check_contradiction(a: &[EnsembleStatement]) -> bool {
    use InternedStatement::*;
    let (mut cnt_vars, a) = InternedStatement::intern_array(a);
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
            True => (),
            False => return true,
        }
    }
    let (mut scc, edges) = strong_components(&edges);
    for x in scc.len()..cnt_vars {
        scc.push(x);
    }
    let it = m.into_iter().map(|((x, y), b)| ((scc[x], scc[y]), b));
    let mut m = HashMap::new();
    for ((a, b), v) in it {
        if m.get(&(a, b)) == Some(&!v) {
            return true;
        }
        m.insert((a, b), v);
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

fn strong_components(edges: &[Vec<usize>]) -> (Vec<usize>, Vec<Vec<usize>>) {
    let n = edges.len();
    let mut reachable = vec![vec![false; n]; n];
    fn dfs(i: usize, edges: &[Vec<usize>], mark: &mut Vec<bool>) {
        if mark[i] {
            return;
        }
        mark[i] = true;
        for j in &edges[i] {
            dfs(*j, edges, mark);
        }
    }
    for (x, r) in reachable.iter_mut().enumerate() {
        dfs(x, edges, r);
    }
    let scc = (0..n)
        .map(|x| {
            (0..x)
                .find(|y| reachable[x][*y] && reachable[*y][x])
                .unwrap_or(x)
        })
        .collect::<Vec<_>>();
    let reach_edges = (0..n)
        .map(|x| {
            if scc[x] != x {
                return vec![];
            }
            scc.iter()
                .enumerate()
                .filter(|(a, b)| a == *b && reachable[x][*a])
                .map(|x| x.0)
                .collect()
        })
        .collect();
    (scc, reach_edges)
}

fn negator(x: EnsembleStatement) -> EnsembleStatement {
    use EnsembleStatement::*;
    match x {
        IsMember(a, b) => IsNotMember(a, b),
        IsNotMember(a, b) => IsMember(a, b),
        IsSubset(a, b) => IsNotSubset(a, b),
        IsNotSubset(a, b) => IsSubset(a, b),
        True => False,
        False => True,
    }
}

fn pre_process_frame(frame: Frame) -> Frame {
    let mut intros_flag = false;
    let frame = match apply(frame.clone(), vec!["included_fold".to_string()].into_iter()) {
        Ok(x) if x.len() == 1 => {
            intros_flag = true;
            x.into_iter().next().unwrap()
        }
        _ => frame,
    };
    let frame = match apply(
        frame.clone(),
        vec!["set_equality_forall".to_string()].into_iter(),
    ) {
        Ok(x) if x.len() == 1 => {
            intros_flag = true;
            x.into_iter().next().unwrap()
        }
        _ => frame,
    };
    if intros_flag {
        match intros(frame.clone(), vec![].into_iter()) {
            Ok(x) if x.len() == 1 => x.into_iter().next().unwrap(),
            _ => frame,
        }
    } else {
        frame
    }
}

pub fn auto_set(frame: Frame) -> Result<Vec<Frame>> {
    let frame = pre_process_frame(frame);
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
        fail("∀ T: U, ∀ A B C: set T, A ⊆ C ∪ B -> A ⊆ C ∨ A ⊆ B");
        success("∀ T: U, ∀ A B: set T, A ⊆ A ∪ B");
    }

    #[test]
    fn intersect() {
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∩ B → a ∈ A");
        fail("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A → a ∈ A ∩ B");
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∩ B → a ∈ B");
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∧ a ∈ B → a ∈ A ∩ B");
        success("∀ T: U, ∀ A B C: set T, A ⊆ C ∩ B -> A ⊆ C ∧ A ⊆ B");
    }

    #[test]
    fn intersect_union() {
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A ∩ B -> a ∈ A ∪ B ");
    }

    #[test]
    fn with_logic() {
        success(
            "∀ T: U, ∀ a: T, ∀ A1 A2 B1 B2: set T,\
            a ∈ A1 ∩ B1 ∨ a ∈ A2 ∩ B2 -> a ∈ A1 ∪ A2 ∧ a ∈ B1 ∪ B2",
        );
    }

    #[test]
    fn set_minus() {
        success("∀ T: U, ∀ A B: set T, B ⊆ A -> ∀ x: T, x ∈ A -> x ∈ B ∪ A ∖ B");
    }

    #[test]
    fn empty() {
        success("∀ T: U, ∀ a: T, a ∈ {} -> False");
        success("∀ T: U, ∀ A: set T, {} ⊆ A");
    }

    #[test]
    fn equality() {
        success("∀ T: U, ∀ A B: set T, A = B -> A ∈ {B}");
        success("∀ T: U, ∀ a: T, ∀ A B: set T, A = B -> a ∈ A -> a ∈ B");
        success("∀ T: U, ∀ S: set (set T), ∀ A B: set T, A = B -> A ∈ S -> B ∈ S");
        success(
            "∀ T: U, ∀ S: set (set T), ∀ A B C: set T,\
            A ⊆ B -> B ⊆ C -> C ⊆ A -> A ∈ S -> B ∈ S ∧ C ∈ S",
        );
    }

    #[test]
    fn singleton() {
        success("2 ∈ {2}");
        success("2 ∈ {1, 2, 3}");
        success("∀ T: U, ∀ a: T, a ∈ {a}");
        fail("∀ T: U, ∀ a b: T, a ∈ {b}");
        success("∀ T: U, ∀ a b: T, a ∈ {a, b}");
        success("∀ T: U, ∀ a: T, ∀ A B: set T, a ∈ A -> {a} ⊆ A");
        success("∀ T: U, ∀ a b: T, ∀ A B: set T, a ∈ A -> b ∈ A -> {a, b} ⊆ A");
        success("{2} ⊆ {2}");
        success("{2} ⊆ {2, 3}");
        fail("{2, 3} ⊆ {2}");
        success("{2, 3} ⊆ {2, 3}");
        success("{2, 3} ⊆ {2, 5, 3}");
        success("∀ T: U, ∀ a b: T, a ∈ {b} -> a = b");
        success("∀ a: ℤ, a ∈ {2} -> a = 2");
        success("∀ a: ℤ, a ∈ {2, 3} -> a = 2 ∨ a = 3");
    }

    #[test]
    fn a_random_test() {
        success(
            "∀ T: U, ∀ a: T, ∀ A B C D E F: set T,\
        a ∈ C -> a ∈ E -> a ∈ F -> a ∈ (A ∪ (B ∪ C)) ∩ (D ∪ (E ∩ F))",
        );
        fail(
            "∀ T: U, ∀ a: T, ∀ A B C D E F: set T,\
        a ∈ C -> a ∈ E -> a ∈ (A ∪ (B ∪ C)) ∩ (D ∪ (E ∩ F))",
        );
    }

    #[test]
    fn remove_element() {
        success("∀ T: U, ∀ a: T, ∀ S: set T, a ∈ S → {a} ∪ S ∖ {a} = S")
    }

    #[test]
    fn imp_and_subset() {
        success(
            "∀ T: U, ∀ A B C D: set T, A ⊆ B -> (A ⊆ B -> B ⊆ C) ->\
        (B ⊆ C -> C ⊆ D) -> A ⊆ D",
        );
        fail(
            "∀ T: U, ∀ A B C D: set T, (A ⊆ B -> B ⊆ C) ->\
        (B ⊆ C -> C ⊆ D) -> A ⊆ D",
        );
    }
}
