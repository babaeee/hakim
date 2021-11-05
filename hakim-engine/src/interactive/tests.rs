use super::{Engine, Session};

fn build_engine() -> Engine {
    let mut eng = Engine::default();
    eng.load_library("Arith").unwrap();
    eng.load_library("Logic").unwrap();
    eng.load_library("Eq").unwrap();
    eng.load_library("Sigma").unwrap();
    eng.load_library("Induction").unwrap();
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

pub fn run_interactive_to_end(goal: &str, tactics: &str) {
    let session = run_interactive(goal, tactics);
    if !session.is_finished() {
        panic!("Goal not solved:\n{}", session.monitor_string());
    }
}

pub fn run_interactive_to_fail(goal: &str, tactics: &str, fail_tactic: &str) {
    let mut session = run_interactive(goal, tactics);
    if session.run_tactic(fail_tactic).is_ok() {
        panic!(
            "tactic succeed but we need fail. Current monitor:\n{}",
            session.monitor_string()
        )
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

#[test]
fn forall_not_exist() {
    run_interactive_to_end(
        "∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False",
        r#"
        intros A P fa exi
        apply ex_ind (3:=exi)
        intros exv exv_not_p
        apply (exv_not_p (fa exv))
        "#,
    );
    run_interactive_to_end(
        "∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False",
        r#"
        intros A P fa exi
        apply ex_ind (3:=exi)
        intros exv exv_not_p
        apply exv_not_p
        apply fa
        "#,
    );
}

#[test]
fn sigma_1_n() {
    run_interactive_to_end(
        "∀ n: ℤ, eq ℤ (2 * sigma 0 (n+1) (λ i: ℤ, i)) (n * (n + 1))",
        r#"
        apply (simple_induction 0 (λ n: ℤ, eq ℤ (2 * sigma 0 (n+1) (λ i: ℤ, i)) (n * (n + 1))))
        intros n gam_farz
        add_hyp (eq ℤ (sigma 0 (n + 1) (λ i: ℤ, i) + sigma (n + 1) ((n + 1) + 1) (λ i: ℤ, i)) (sigma 0 ((n + 1) + 1) (λ i: ℤ, i)))
        apply sigma_plus
        rewrite <- H
        add_hyp (eq ℤ (2 * (sigma 0 (n + 1) (λ x0: ℤ, x0) + sigma (n + 1) ((n + 1) + 1) (λ x0: ℤ, x0))) (n * (n + 1) + 2 * (n + 1)))
        rewrite (sigma_atom (n+1) (λ x0: ℤ, x0))
        rewrite <- gam_farz
        ring
        rewrite H0
        ring
        rewrite (sigma_atom 0 (λ x0: ℤ, x0))
        ring
        "#,
    );
}
