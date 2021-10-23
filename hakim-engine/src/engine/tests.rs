use super::Engine;

fn run_interactive_to_end(goal: &str, tactics: &str) {
    let mut eng = Engine::default();
    eng.load_library("Arith").unwrap();
    let mut session = eng.interactive_session(goal).unwrap();
    for tactic in tactics.lines() {
        let tactic = tactic.trim();
        if tactic.is_empty() {
            continue;
        }
        session
            .run_tactic(tactic)
            .map_err(|e| panic!("Error {:?}\nMonitor:\n{}", e, session.monitor_string()))
            .unwrap();
    }
    if !session.is_finished() {
        panic!("Goal not solved:\n{}", session.monitor_string());
    }
}

fn run_interactive_to_fail(goal: &str, tactics: &str, fail_tactic: &str) {
    let eng = Engine::default();
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
fn check_undo() {
    run_interactive_to_end(
        F_EQUAL,
        r#"
    intros t1
    intros t2
    intros f
    intros a
    intros b
    intros bad_name
    Undo
    Undo
    intros c
    Undo
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
    run_interactive_to_fail(
        F_EQUAL,
        r#"
        intros x
        intros y
    "#,
        "intros",
    );
}

#[test]
fn intros_bad_arg() {
    run_interactive_to_fail(F_EQUAL, "", "intros");
    run_interactive_to_fail(F_EQUAL, "", "intros  ");
    run_interactive_to_fail(F_EQUAL, "", "intros x y");
    run_interactive_to_fail(F_EQUAL, "", "intros -2");
    run_interactive_to_fail(F_EQUAL, "", "intros (rewrite x)");
}

#[test]
fn success_ring1() {
    run_interactive_to_end(
        "forall x: ℤ, eq ℤ (x + x) (2 * x)",
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

#[test]
fn success_add_hyp() {
    run_interactive_to_end(
        "forall a b c d: ℤ, a < b -> c < d -> a + c < b + d",
        r#"
        intros a
        intros b
        intros c
        intros d
        intros a_lt_b
        intros c_lt_d
        add_hyp (a + c < b + c)
        apply (lt_plus_r a b c a_lt_b)
        add_hyp (b + c < b + d)
        apply (lt_plus_l c d b c_lt_d)
        apply (lt_trans (a+c) (b+c) (b+d) H H0)
        "#,
    );
}
