use super::{Error::*, Result};
use crate::{
    app_ref,
    brain::{Term, TermRef},
    interactive::Frame,
    library::prelude::set,
    term_ref,
};
use typed_arena::Arena;

#[derive(Debug, Clone)]
enum EnsembleTree<'a> {
    Set(u16),
    Union(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Intersection(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Setminus(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Eq(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Included(&'a EnsembleTree<'a>, &'a EnsembleTree<'a>),
    Inset(u16, &'a EnsembleTree<'a>),
    Outset(u16, &'a EnsembleTree<'a>),
}
use EnsembleTree::*;

type EnsembleArena<'a> = &'a Arena<EnsembleTree<'a>>;

use std::collections::HashMap;
use std::collections::VecDeque;
struct Identifier {
    map: HashMap<TermRef, u16>,
    id_counter: u16,
}
impl Identifier {
    pub fn new() -> Identifier {
        Identifier {
            map: HashMap::new(),
            id_counter: 1,
        }
    }
    pub fn get(&mut self, v: &TermRef) -> u16 {
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
struct Hyps<'a> {
    simple_hyps: HashMap<(u16, u16), i32>,
    ahyps: VecDeque<&'a EnsembleTree<'a>>,
    bhyps: VecDeque<&'a EnsembleTree<'a>>,
}
impl<'a> Hyps<'a> {
    pub fn new() -> Hyps<'a> {
        //map simple form of x ∈ A to (x, A) -> {number of existen prop of this type}
        //minus number mean we have prop of x ∉ A
        let simple_hyps: HashMap<(u16, u16), i32> = HashMap::new();
        //hypothiss that generate two goal
        let bhyps: VecDeque<&EnsembleTree> = VecDeque::new();
        //hyps that not
        let ahyps: VecDeque<&EnsembleTree> = VecDeque::new();
        Hyps {
            simple_hyps,
            ahyps,
            bhyps,
        }
    }
    fn add_hyp(&mut self, h: &'a EnsembleTree<'a>, undo: bool) -> i32 {
        let add = |hyps: &mut VecDeque<&EnsembleTree<'a>>| -> i32 {
            if undo {
                hyps.pop_back();
            } else {
                hyps.push_back(h);
            }
            0
        };
        match h {
            Inset(x, set_x) => {
                match *set_x {
                    Intersection(..) | Setminus(..) => add(&mut self.ahyps),
                    Union(..) => add(&mut self.bhyps),
                    Set(i) => {
                        let counter = self.simple_hyps.entry((*x, *i)).or_insert(0);
                        if undo {
                            (*counter) -= 1;
                        } else {
                            if *counter < 0 {
                                return 1; //found Contradiction
                            }
                            (*counter) += 1;
                        }
                        0
                    }
                    _ => -1, //false input
                }
            }
            Outset(x, set_x) => {
                match *set_x {
                    Union(..) => add(&mut self.ahyps),
                    Intersection(..) | Setminus(..) => add(&mut self.bhyps),
                    Set(i) => {
                        let counter = self.simple_hyps.entry((*x, *i)).or_insert(0);
                        if undo {
                            (*counter) += 1;
                        } else {
                            if *counter > 0 {
                                return 1; //found Contradiction
                            }
                            (*counter) -= 1;
                        }
                        0
                    }
                    _ => -1, //false input
                }
            }
            Eq(..) => add(&mut self.ahyps),
            Included(..) => add(&mut self.bhyps),
            _ => -1,
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
    return arena.alloc(Set(sets_id.get(t)));
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
                    return Some((arena.alloc(Outset(*x, set_a)), ty));
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
                        let tree = Inset(elements_id.get(op1), from_set_type(op2, arena, sets_id));
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
fn dfs<'a>(
    goal: &'a EnsembleTree<'a>,
    arena: EnsembleArena<'a>,
    element_in_goal: u16,
    hyps: &mut Hyps<'a>,
) -> i32 {
    println!("{} {:?}", element_in_goal, goal);
    let mut step1 = |h, g, x| {
        let c = hyps.add_hyp(h, false);
        if c == 0 {
            let c = dfs(g, arena, x, hyps);
            hyps.add_hyp(h, true);
            return c;
        }
        c
    };
    match goal {
        Inset(x, set_x) => {
            match set_x {
                Union(set_a, set_b) => {
                    return step1(
                        arena.alloc(Outset(*x, set_b)),
                        arena.alloc(Inset(*x, set_a)),
                        *x,
                    );
                }
                Set(i) => {
                    if let Some(counter) = hyps.simple_hyps.get(&(*x, *i)) {
                        if *counter > 0 {
                            return 1;
                        }
                    }
                    //set element_in_goal
                    if *x != element_in_goal {
                        return dfs(goal, arena, *x, hyps);
                    }
                }
                _ => (),
            }
        }
        Outset(x, set_a) => {
            return step1(arena.alloc(Inset(*x, set_a)), arena.alloc(Set(0)), *x);
        }
        Included(set_a, set_b) => {
            //bigest u16 value for new id
            return step1(
                arena.alloc(Inset(65535, set_a)),
                arena.alloc(Inset(65535, set_b)),
                65535,
            );
        }
        _ => (),
    }
    if let Some(h) = hyps.ahyps.pop_front() {
        let mut step2 = |h1, h2| {
            let c1 = hyps.add_hyp(h1, false);
            if c1 == 0 {
                let mut c2 = hyps.add_hyp(h2, false);
                if c2 == 0 {
                    c2 = dfs(goal, arena, element_in_goal, hyps);
                    hyps.add_hyp(h2, true);
                }
                hyps.add_hyp(h1, true);
                return c2;
            }
            c1
        };
        if let Inset(x, set_x) = h {
            if let Intersection(set_a, set_b) = *set_x {
                return step2(arena.alloc(Inset(*x, set_a)), arena.alloc(Inset(*x, set_b)));
            } else if let Setminus(set_a, set_b) = *set_x {
                return step2(
                    arena.alloc(Inset(*x, set_a)),
                    arena.alloc(Outset(*x, set_b)),
                );
            }
        } else if let Outset(x, set_x) = h {
            if let Union(set_a, set_b) = *set_x {
                return step2(
                    arena.alloc(Outset(*x, set_a)),
                    arena.alloc(Outset(*x, set_b)),
                );
            }
        } else if let Eq(set_a, set_b) = h {
            return step2(
                arena.alloc(Included(set_a, set_b)),
                arena.alloc(Included(set_b, set_a)),
            );
        }
        hyps.ahyps.push_front(h);
    }

    let mut step3 = |g1, g2, x| {
        let c = dfs(g1, arena, x, hyps);
        if c == 1 {
            return dfs(g2, arena, x, hyps);
        }
        c
    };
    match goal.clone() {
        Inset(x, set_x) => match *set_x {
            Intersection(set_a, set_b) => {
                return step3(
                    arena.alloc(Inset(x, set_a)),
                    arena.alloc(Inset(x, set_b)),
                    x,
                );
            }
            Setminus(set_a, set_b) => {
                return step3(
                    arena.alloc(Inset(x, set_a)),
                    arena.alloc(Outset(x, set_b)),
                    x,
                );
            }
            _ => (),
        },
        Eq(set_a, set_b) => {
            return step3(
                arena.alloc(Included(set_a, set_b)),
                arena.alloc(Included(set_b, set_a)),
                element_in_goal,
            );
        }
        _ => (),
    }
    if let Some(h) = hyps.bhyps.pop_front() {
        let mut step4 = |h1, h2| {
            let mut c = hyps.add_hyp(h1, false);
            if c == 0 || c == 1 {
                if c == 0 {
                    c = dfs(goal, arena, element_in_goal, hyps);
                }
                hyps.add_hyp(h1, true);

                if c == 1 {
                    c = hyps.add_hyp(h2, false);
                    if c == 0 || c == 1 {
                        if c == 0 {
                            c = dfs(goal, arena, element_in_goal, hyps);
                        }
                        hyps.add_hyp(h2, true);
                        return c;
                    }
                    return c;
                }
                return c;
            }
            c
        };
        if let Inset(x, set_x) = h {
            if let Union(set_a, set_b) = *set_x {
                return step4(arena.alloc(Inset(*x, set_a)), arena.alloc(Inset(*x, set_b)));
            }
        } else if let Outset(x, set_x) = h {
            if let Intersection(set_a, set_b) = set_x {
                return step4(
                    arena.alloc(Outset(*x, set_a)),
                    arena.alloc(Outset(*x, set_b)),
                );
            } else if let Setminus(set_a, set_b) = set_x {
                return step4(
                    arena.alloc(Outset(*x, set_a)),
                    arena.alloc(Inset(*x, set_b)),
                );
            }
        } else if let Included(set_a, set_b) = h {
            //can we add element_in_goal ∈ A too but no need
            //println!("incl {} {:?} {:?}", element_in_goal, set_b, set_a);
            return step4(
                arena.alloc(Inset(element_in_goal, set_b)),
                arena.alloc(Outset(element_in_goal, set_a)),
            );
        }
        hyps.bhyps.push_front(h);
    }
    return 0; //date no compelete
}
pub fn auto_set(frame: Frame) -> Result<Vec<Frame>> {
    let arena = &Arena::with_capacity(32);
    let mut elements_id: Identifier = Identifier::new();
    let mut sets_id: Identifier = Identifier::new();

    if let Some((goal, goal_ty)) = from_prop_type(frame.goal, arena, &mut elements_id, &mut sets_id)
    {
        let mut hyps = Hyps::new();

        for val in frame.hyps.values() {
            if let Some((x, ty)) =
                from_prop_type(val.clone(), arena, &mut elements_id, &mut sets_id)
            {
                if goal_ty == ty && hyps.add_hyp(x, false) != 0 {
                    return Err(BadHyp("can,t match", val.clone()));
                }
            }
        }
        let ans = dfs(goal, arena, 65535, &mut hyps);
        if ans == 1 {
            return Ok(vec![]);
        } else if ans == 0 {
            return Err(CanNotSolve("auto_set"));
        } else if ans == -1 {
            return Err(BadGoal("can,t match hyp"));
        }
    }
    Err(BadGoal("can,t solve this type"))
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn success1() {
        run_interactive_to_end(
            "∀ T: U, ∀ a: T, ∀ A B C: set T, a ∈ C ∩ B -> a ∈ A ∩ C -> a ∈ C ∩ B ∩ A",
            "intros\nauto_set",
        );
    }

    #[test]
    #[ignore]
    fn success2() {
        run_interactive_to_end(
            "∀ T: U, ∀ a: T, ∀ A B C D E F: set T, a ∈ C -> a ∈ E -> a ∈ (A ∪ (B ∪ C)) ∩ (D ∪ (E ∩ F))",
            "intros\nauto_set",
        );
    }
}
