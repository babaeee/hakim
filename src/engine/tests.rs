use super::Engine;

fn run_interactive_to_end(goal: &str, tactics: &str) {
    let mut eng = Engine::default();
    let mut session = eng.interactive_session(goal);
    for tactic in tactics.lines() {
        let tactic = tactic.trim();
        if tactic.is_empty() {
            continue;
        }
        session.run_tactic(tactic).unwrap();
    }
    if !session.is_finished() {
        panic!("Goal not solved:\n{}", session.monitor_string());        
    }
}

#[test]
fn proof_f_equal() {
    run_interactive_to_end("forall a b: U, forall f: forall x: a, b, forall x y: a, forall p: eq a x y, eq b (f x) (f y)", r#"
    intros t1
    intros t2
    intros f
    intros a
    intros b
    intros eq_proof
    rewrite eq_proof
    apply (eq_refl t2 (f b))
    "#);
}
