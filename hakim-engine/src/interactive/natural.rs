use crate::interactive::smart_split;

use super::{Frame, Session};

enum ProofTree {
    RemainingGoal(Frame),
    Tactic {
        frame: Frame,
        tactic: String,
        children: Vec<usize>,
    },
}

impl ProofTree {
    fn frame(&self) -> &Frame {
        match self {
            RemainingGoal(frame) => frame,
            Tactic { frame, .. } => frame,
        }
    }
    fn goal_string(&self) -> String {
        let f = self.frame();
        f.engine.pretty_print(&f.goal)
    }
}

use ProofTree::*;

impl ProofTree {
    fn from(session: Session) -> Vec<Self> {
        let mut it = session.history.into_iter();
        let mut r = vec![RemainingGoal(
            it.next()
                .unwrap()
                .snapshot
                .frames
                .into_iter()
                .next()
                .unwrap(),
        )];
        let mut going = vec![0];
        let mut pf = 1;
        for h in it {
            if let Some(x) = h.tactic.strip_prefix("Switch ") {
                let x: usize = x.parse().unwrap();
                let len = going.len();
                going.swap(len - 1, len - 1 - x);
                continue;
            }
            let now = going.pop().unwrap();
            let frames = h.snapshot.frames;
            let cnt = frames.len() + 1 - pf;
            pf = frames.len();
            let children: Vec<_> = frames
                .into_iter()
                .rev()
                .take(cnt)
                .map(|x| {
                    r.push(RemainingGoal(x));
                    r.len() - 1
                })
                .collect();
            going.extend(children.iter().rev());
            r[now] = Tactic {
                frame: r[now].frame().clone(),
                tactic: h.tactic,
                children,
            };
        }
        r
    }
}

pub enum NaturalProof {
    Statement(String),
    ParentChild(Box<NaturalProof>, Box<NaturalProof>),
    Sibling(Box<NaturalProof>, Box<NaturalProof>),
}

use NaturalProof::*;

impl From<Session> for NaturalProof {
    fn from(session: Session) -> Self {
        fn sibl(it: impl Iterator<Item = Box<NaturalProof>>) -> Box<NaturalProof> {
            it.reduce(|a, b| Box::new(Sibling(a, b))).unwrap()
        }
        fn intros(cur: &Frame, next: &Frame) -> String {
            let mut r = String::new();
            let hyps_ordered = next.order_hyps();
            for hn in &hyps_ordered {
                if cur.hyps.contains_key(hn) {
                    continue;
                }
                if next.deny_dependency(hn).is_ok() {
                    continue;
                }
                let ty = next.engine.pretty_print(next.hyps.get(hn).unwrap());
                r += &format!("$one {} $random_like {}, ", ty, hn);
            }
            r += "$we_consider. $we_know ";
            for hn in &hyps_ordered {
                if cur.hyps.contains_key(hn) {
                    continue;
                }
                if next.deny_dependency(hn).is_err() {
                    continue;
                }
                let ty = next.engine.pretty_print(next.hyps.get(hn).unwrap());
                r += &format!("{} ($hyp {}) $and ", ty, hn);
            }
            r += "$its_enough_to_proof ";
            r += &next.engine.pretty_print(&next.goal);
            r
        }
        fn apply_hyp(lem: &str, hyp: &str, next: usize, pt: &[ProofTree]) -> NaturalProof {
            let ty = pt[next].frame().hyps.get(hyp).unwrap();
            let ty = pt[next].frame().engine.pretty_print(ty);
            Sibling(
                Box::new(Statement(format!(
                    "$inl_apply_on_hyp<${}$,{}$,{}$>",
                    lem, hyp, ty
                ))),
                Box::new(dfs(next, pt)),
            )
        }
        fn apply_goal(lem: &str, children: &[usize], pt: &[ProofTree]) -> NaturalProof {
            match children {
                [] => Statement(format!("$by {} $goal_solved", lem)),
                [x] => Sibling(
                    Box::new(Statement(format!(
                        "$by {} $its_enough_to_proof {}",
                        lem,
                        pt[*x].goal_string()
                    ))),
                    Box::new(dfs(*x, pt)),
                ),
                x => {
                    let parent = Box::new(Statement(format!(
                        "$by {} $its_enough_to_proof_following",
                        lem
                    )));
                    let childs = sibl(x.iter().map(|&x| {
                        Box::new(ParentChild(
                            Box::new(Statement(pt[x].goal_string())),
                            Box::new(dfs(x, pt)),
                        ))
                    }));
                    ParentChild(parent, childs)
                }
            }
        }
        fn fallback(tactic: &str, children: &[usize], pt: &[ProofTree]) -> NaturalProof {
            match children {
                [] => Statement(tactic.to_string()),
                [x] => Sibling(
                    Box::new(Statement(tactic.to_string())),
                    Box::new(dfs(*x, pt)),
                ),
                x => {
                    let parent = Box::new(Statement(tactic.to_string()));
                    let childs = sibl(x.iter().map(|&x| Box::new(dfs(x, pt))));
                    ParentChild(parent, childs)
                }
            }
        }
        fn dfs(x: usize, pt: &[ProofTree]) -> NaturalProof {
            let x = &pt[x];
            match x {
                RemainingGoal(f) => Statement(format!("$goal {:?} $not_solved", f.goal)),
                Tactic {
                    frame,
                    tactic,
                    children,
                } => {
                    let tacvec = smart_split(tactic);
                    match tacvec[0].as_str() {
                        "intros" => Sibling(
                            Box::new(Statement(intros(frame, pt[children[0]].frame()))),
                            Box::new(dfs(children[0], pt)),
                        ),
                        "apply" if tacvec.len() == 2 => apply_goal(&tacvec[1], children, pt),
                        "apply" if tacvec.len() == 4 => {
                            apply_hyp(&tacvec[1], &tacvec[3], children[0], pt)
                        }
                        "destruct" if tacvec.len() == 4 => {
                            if tacvec[3] == "(or_ind ? ?)" {
                                let h = &tacvec[1];
                                let parent = Box::new(Statement(format!("$case_on_hyp<${}$>", h)));
                                let childs = sibl(children.iter().map(|&x| {
                                    Box::new(ParentChild(
                                        Box::new(Statement(format!(
                                            "$case {:?}",
                                            pt[x].frame().hyps.get(h).unwrap()
                                        ))),
                                        Box::new(dfs(x, pt)),
                                    ))
                                }));
                                ParentChild(parent, childs)
                            } else {
                                fallback(tactic, children, pt)
                            }
                        }
                        x @ ("lia" | "ring" | "auto_set" | "assumption") => {
                            Statement(format!("$inl_by_{}", x))
                        }
                        _ => fallback(tactic, children, pt),
                    }
                }
            }
        }
        let pt = ProofTree::from(session);
        dfs(0, &pt)
    }
}

impl NaturalProof {
    pub fn into_string(self, depth: usize, r: &mut String) {
        match self {
            NaturalProof::Statement(s) => {
                *r += &"  ".repeat(depth);
                *r += "* ";
                *r += &s;
                *r += "\n";
            }
            NaturalProof::ParentChild(p, c) => {
                p.into_string(depth, r);
                c.into_string(depth + 1, r);
            }
            NaturalProof::Sibling(a, b) => {
                a.into_string(depth, r);
                b.into_string(depth, r);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive, EngineLevel};

    #[test]
    fn no_panic() {
        let se = run_interactive(
            "forall a b c d: ℤ, a < b -> c < d -> a + c < b + d",
            r#"
            intros a b c d a_lt_b c_lt_d
            add_hyp (a + c < b + c)
            apply lt_plus_r
            apply a_lt_b
            add_hyp (b + c < b + d)
            apply lt_plus_l
            apply c_lt_d"#,
            EngineLevel::Full,
        );
        se.natural();
    }
}
