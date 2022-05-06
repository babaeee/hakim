use super::{proof_tree::ProofTree, Frame, Session, Snapshot};

fn try_tactic_list(frame: Frame, mut tactics: Vec<String>) -> Option<Vec<String>> {
    let mut snap = Snapshot::from(frame);
    for (i, t) in tactics.iter().enumerate() {
        if let Ok(next_snap) = snap.run_tactic(t) {
            if next_snap.is_finished() {
                tactics.truncate(i + 1);
                return Some(tactics);
            }
            snap = next_snap;
        }
    }
    None
}

pub fn history_lookup_auto(session: Session) -> Option<Vec<String>> {
    let target = session.last_snapshot().frames.last()?.clone();
    let tree = ProofTree::from(session);
    let r = tree
        .iter()
        .filter(|&(i, pn)| pn.frame().goal == target.goal && tree.is_solved(i))
        .find_map(|(i, _)| try_tactic_list(target.clone(), tree.tactics(i)));
    r
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive;

    fn check_history(goal: &str, tactics: &str, expected_result: &str) {
        let session = run_interactive(goal, tactics, crate::interactive::tests::EngineLevel::Full);
        let r = session
            .history_based_auto()
            .expect("no solution found in history");
        assert_eq!(
            r,
            expected_result
                .lines()
                .map(|x| x.trim())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn simple() {
        check_history(
            "∀ A: Universe, A -> A ∧ A",
            r#"
        intros A H
        apply and_intro
        apply H
        "#,
            "apply H",
        )
    }
}
