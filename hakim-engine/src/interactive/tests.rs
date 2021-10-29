use super::{Engine, Session};

fn build_engine() -> Engine {
    let mut eng = Engine::default();
    eng.load_library("Arith").unwrap();
    eng.load_library("Logic").unwrap();
    eng
}

pub fn run_interactive(goal: &str, tactics: &str) -> Session {
    let eng = build_engine();
    let mut session = eng.interactive_session(goal).unwrap();
    for tactic in tactics.lines() {
        let tactic = tactic.trim();
        if tactic.is_empty() {
            continue;
        }
        session
            .run_tactic(tactic)
            .map_err(|e| {
                panic!(
                    "Error {:?}\nTactic: {}\nMonitor:\n{}",
                    e,
                    tactic,
                    session.monitor_string()
                )
            })
            .unwrap();
    }
    session
}

fn run_interactive_to_end(goal: &str, tactics: &str) {
    let session = run_interactive(goal, tactics);
    if !session.is_finished() {
        panic!("Goal not solved:\n{}", session.monitor_string());
    }
}

fn run_interactive_to_fail(goal: &str, tactics: &str, fail_tactic: &str) {
    let mut session = run_interactive(goal, tactics);
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
        "apply",
    );
}

#[test]
fn intros_bad_arg() {
    run_interactive_to_fail(F_EQUAL, "", "intros x 5");
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

#[test]
fn success_apply_implicit() {
    run_interactive_to_end(
        "forall a b c d: ℤ, a < b -> c < d -> a + c < b + d",
        r#"
        intros a b c d a_lt_b c_lt_d
        add_hyp (a + c < b + c)
        apply lt_plus_r
        apply a_lt_b
        add_hyp (b + c < b + d)
        apply lt_plus_l
        apply c_lt_d
        apply (lt_trans (a+c) (b+c) (b+d) H H0)
        "#,
    );
}

#[test]
fn apply_implicit_fail_instance() {
    run_interactive_to_fail(
        "forall a b c d: ℤ, a < b -> c < d -> a + c < b + d",
        r#"
        intros a b c d a_lt_b c_lt_d
        add_hyp (a + c < b + c)
        apply lt_plus_r
        apply a_lt_b
        add_hyp (b + c < b + d)
        apply lt_plus_l
        apply c_lt_d"#,
        "apply lt_trans",
    );
}
// ∀ x0: U, ∀ x1: x0 → U, (∀ x2: x0, x1 x2) → (x0 → ∃ x2: x0, x1 x2)

#[test]
fn exists_simple() {
    run_interactive_to_end(
        "∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, P x",
        r#"
        intros A P pall a
        apply (ex_intro A P a)
        apply pall
        "#,
    );
    run_interactive_to_fail(
        "∀ A: U, ∀ P Q: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, Q x",
        r#"
        intros A P Q pall a
        "#,
        "apply (ex_intro A P a)",
    );
    run_interactive_to_fail(
        "∀ A: U, ∀ P Q: A -> U, (∀ x: A, P x) -> A -> ∃ x: A, Q x",
        r#"
        intros A P Q pall a
        apply (ex_intro A Q a)
        "#,
        "apply pall",
    );
}

#[test]
fn exists_number() {
    run_interactive_to_end(
        "∀ a: ℤ, ∃ b: ℤ, a < b",
        r#"
        intros a
        apply (ex_intro ℤ (λ t: ℤ, a < t) (a + 1))
        add_hyp (eq ℤ a (a+0))
        ring
        rewrite H
        add_hyp (eq ℤ ((a+0)+1) (a+1))
        ring
        rewrite H0
        apply lt_plus_l
        apply lt_0_1
        "#,
    )
}

#[test]
fn exists_destruct() {
    run_interactive_to_end(
        "∀ P: ℤ -> U, (∀ x: ℤ, P x -> P (2*x)) -> (∃ b: ℤ, P b) -> ∃ b: ℤ, P (2*b)",
        r#"
        intros P px_p2x exP
        apply ex_ind (3:=exP)
        intros exP_value exP_proof
        apply ex_intro (3:=exP_value)
        apply px_p2x
        apply exP_proof
        "#,
    )
}
