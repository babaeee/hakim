use std::fmt::{Display, Formatter};

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

impl Monitor {
    #[cfg(test)]
    fn hyp_names(&self) -> Vec<String> {
        match self {
            Running { hyps, .. } => hyps.iter().map(|(x, _)| x.clone()).collect(),
            Finished => unreachable!(),
        }
    }
}

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

impl Snapshot {
    pub fn monitor(&self) -> Monitor {
        if self.is_finished() {
            return Monitor::Finished;
        }
        let goals = self
            .frames
            .iter()
            .map(|x| x.engine.pretty_print_to_html(&x.goal))
            .collect();
        let frame = self.frames.last().unwrap();
        let hyps = frame
            .hyps
            .iter()
            .map(|x| (x.name.clone(), frame.engine.pretty_print_to_html(&x.ty)))
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
        assert_eq!(x.monitor().hyp_names(), vec!["A", "P", "H", "H0"]);
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
            x.monitor().hyp_names(),
            vec!["A", "P", "H", "H0_value", "H0_proof"]
        );
    }
}
