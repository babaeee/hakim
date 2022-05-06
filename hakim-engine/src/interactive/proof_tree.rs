pub enum ProofNode {
    RemainingGoal(Frame),
    Tactic {
        frame: Frame,
        tactic: String,
        children: Vec<usize>,
    },
}

pub struct ProofTree(pub Vec<ProofNode>);

impl ProofTree {
    pub fn iter(&self) -> impl Iterator<Item = (usize, &ProofNode)> {
        self.0.iter().enumerate()
    }

    pub fn is_solved(&self, i: usize) -> bool {
        match &self.0[i] {
            RemainingGoal(_) => false,
            Tactic { children, .. } => children.iter().all(|i| self.is_solved(*i)),
        }
    }

    pub(crate) fn tactics(&self, i: usize) -> Vec<String> {
        let mut v = vec![];
        fn dfs(this: &ProofTree, i: usize, v: &mut Vec<String>) {
            if let Tactic {
                children, tactic, ..
            } = &this.0[i]
            {
                v.push(tactic.clone());
                for c in children {
                    dfs(this, *c, v);
                }
            }
        }
        dfs(self, i, &mut v);
        v
    }
}

impl ProofNode {
    pub fn frame(&self) -> &Frame {
        match self {
            RemainingGoal(frame) => frame,
            Tactic { frame, .. } => frame,
        }
    }
    pub fn goal_string(&self) -> String {
        let f = self.frame();
        f.engine.pretty_print(&f.goal)
    }
}

use ProofNode::*;

use super::{Frame, Session};

impl From<Session> for ProofTree {
    fn from(session: Session) -> Self {
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
        Self(r)
    }
}
