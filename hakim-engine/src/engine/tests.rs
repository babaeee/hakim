use super::Engine;

fn run_interactive_to_end(goal: &str, tactics: &str) {
    let mut eng = Engine::default();
    let mut session = eng.interactive_session(goal).unwrap();
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

fn run_interactive_to_fail(goal: &str, tactics: &str, fail_tactic: &str) {
    let mut eng = Engine::default();
    let mut session = eng.interactive_session(goal).unwrap();
    for tactic in tactics.lines() {
        let tactic = tactic.trim();
        if tactic.is_empty() {
            continue;
        }
        session.run_tactic(tactic).unwrap();
    }
    match session.run_tactic(fail_tactic) {
        Ok(_) => panic!(
            "tactic succeed but we need fail. Current monitor:\n{}",
            session.monitor_string()
        ),
        Err(_) => (),
    }
}

const F_EQUAL: &str =
    "forall a b: U, forall f: forall x: a, b, forall x y: a, forall p: eq a x y, eq b (f x) (f y)";

#[test]
fn proof_f_equal() {
    run_interactive_to_end(
        F_EQUAL,
        r#"
    intros t1
    intros t2
    intros f
    intros a
    intros b
    intros eq_proof
    rewrite eq_proof
    apply (eq_refl t2 (f b))
    "#,
    );
}

#[test]
fn duplicate_hyp() {
    run_interactive_to_fail(F_EQUAL, "intros x", "intros x");
}

#[test]
fn dont_panic1() {
    run_interactive_to_fail(
        F_EQUAL,
        r#"
        intros x
        intros y
        intros f
        intros a
        intros b
        intros p
    "#,
        "rewrite (eq_switch p)",
    );
}

#[test]
fn success_ring1() {
    run_interactive_to_end(
        "forall x: ℤ, eq ℤ (plus x x) (mult 2 x)",
        r#"
        intros x
        ring
        "#,
    );
}

#[test]
fn success_ring2() {
    run_interactive_to_end(
        "forall a b: ℤ, eq ℤ (mult (plus a b) (plus a b)) \
        (plus (mult a a) (plus (mult 2 (mult a b)) (mult b b)))",
        r#"
        intros a
        intros b
        ring
        "#,
    );
}
