use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap},
    fmt::{Display, Formatter},
};

use crate::brain::map_reduce_axiom;

use super::*;

#[derive(Serialize, Deserialize)]
pub enum Monitor {
    Running {
        hyps: Vec<(String, String)>,
        goals: Vec<String>,
    },
    Finished,
}

use Monitor::*;

impl Display for Monitor {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Finished => write!(f, "No more subgoals."),
            Running { hyps, goals } => {
                let goal_count = goals.len();
                for (name, ty) in hyps {
                    writeln!(f, " {}: {}", name, ty)?;
                }
                for (i, goal) in goals.iter().enumerate() {
                    writeln!(
                        f,
                        "--------------------------------------------({}/{})",
                        i + 1,
                        goal_count
                    )?;
                    writeln!(f, "    {}", goal)?;
                }
                Ok(())
            }
        }
    }
}

impl Frame {
    pub fn order_hyps(&self) -> Vec<String> {
        let frame = self;
        let id_map = {
            let mut x = HashMap::<String, usize>::new();
            for (i, (hyp, _)) in frame.hyps.iter().enumerate() {
                x.insert(hyp.clone(), i);
            }
            x
        };
        let n = frame.hyps.len();
        let mut edge = vec![vec![]; n];
        let mut cnt = vec![0; n];
        for (i, (_, ty)) in frame.hyps.iter().enumerate() {
            map_reduce_axiom(
                ty,
                &mut |x| {
                    let j = *id_map.get(x)?;
                    edge[j].push(i);
                    cnt[i] += 1;
                    Some(())
                },
                &|_, _| (),
            );
        }
        let mut queue = BinaryHeap::new();
        let hyp_vec: Vec<_> = frame.hyps.iter().map(|(a, _)| a).collect();
        cnt.iter().enumerate().filter(|x| *x.1 == 0).for_each(|x| {
            queue.push(Reverse(hyp_vec[x.0]));
        });
        let mut r = vec![];
        while let Some(Reverse(x)) = queue.pop() {
            r.push(x.clone());
            let x = *id_map.get(x).unwrap();
            for &y in &edge[x] {
                cnt[y] -= 1;
                if cnt[y] == 0 {
                    queue.push(Reverse(hyp_vec[y]));
                }
            }
        }
        r
    }
}

impl Snapshot {
    pub fn monitor(&self) -> Monitor {
        if self.is_finished() {
            return Monitor::Finished;
        }
        let goals = self
            .frames
            .iter()
            .map(|x| x.engine.pretty_print(&x.goal))
            .collect();
        let frame = self.frames.last().unwrap();
        let hyps = frame
            .order_hyps()
            .into_iter()
            .map(|x| {
                let rc = frame.hyps.get(&x).unwrap();
                (x, frame.engine.pretty_print(rc))
            })
            .collect();
        Monitor::Running { goals, hyps }
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive, EngineLevel};

    #[test]
    fn dependecy_order1() {
        let x = run_interactive(
            "∀ A: Universe, ∀ P: A → Universe, (∀ x: A, P x) → (∃ x: A, P x → False) → False",
            "intros",
            EngineLevel::Full,
        );
        assert_eq!(
            x.monitor_string(),
            r#" A: Universe
 P: A → Universe
 H: ∀ x: A, P x
 H0: ∃ x: A, ~ P x
--------------------------------------------(1/1)
    False
"#
        );
    }

    #[test]
    fn dependecy_order2() {
        let x = run_interactive(
            "∀ A: Universe, ∀ P: A → Universe, (∀ x: A, P x) → (∃ x: A, P x → False) → False",
            r#"
            intros
            apply (ex_ind ? ? H0)
            remove_hyp H0
            intros H0_value H0_proof
            "#,
            EngineLevel::Full,
        );
        assert_eq!(
            x.monitor_string(),
            r#" A: Universe
 H0_value: A
 P: A → Universe
 H: ∀ x: A, P x
 H0_proof: ~ P H0_value
--------------------------------------------(1/1)
    False
"#
        );
    }
}
