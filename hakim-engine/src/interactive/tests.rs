use std::cell::Cell;

use crate::interactive::tactic::Error;

use super::{Engine, Session};

#[derive(PartialEq, Eq)]
pub enum EngineLevel {
    Empty,
    Full,
}

thread_local! {
    static ENGINE_PARAMS: Cell<String>  = Cell::new(String::new());
}

// this function is only for single threaded testing!!!!
pub fn with_params(params: &str, work: impl FnOnce()) {
    ENGINE_PARAMS.with(|x| {
        x.set(params.to_string());
    });
    work();
    ENGINE_PARAMS.with(|x| x.take());
}

fn build_engine(level: EngineLevel) -> Engine {
    let mut eng = Engine::new(&ENGINE_PARAMS.with(|x| {
        let s = x.take();
        x.set(s.clone());
        s
    }));
    if level == EngineLevel::Empty {
        return eng;
    }
    eng.load_library("Arith").unwrap();
    eng.load_library("Logic").unwrap();
    eng.load_library("Eq").unwrap();
    eng.load_library("Sigma").unwrap();
    eng.load_library("Induction").unwrap();
    eng.load_library("Set").unwrap();
    eng
}

pub fn run_interactive(goal: &str, tactics: &str, level: EngineLevel) -> Session {
    let eng = build_engine(level);
    let mut session = eng
        .interactive_session(goal)
        .expect("fail to start session");
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
    let session = run_interactive(goal, tactics, EngineLevel::Full);
    if !session.is_finished() {
        panic!("Goal not solved:\n{}", session.monitor_string());
    }
}

pub fn run_interactive_to_fail(goal: &str, tactics: &str, fail_tactic: &str) {
    let mut session = run_interactive(goal, tactics, EngineLevel::Full);
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
fn dont_start_with_wild() {
    let eng = build_engine(EngineLevel::Full);
    assert!(matches!(
        eng.interactive_session("?"),
        Err(super::Error::GoalWithWildCard(_))
    ));
    assert!(matches!(
        eng.interactive_session("{} ⊆ {}"),
        Err(super::Error::GoalWithWildCard(_))
    ));
}

#[test]
fn bad_tactic() {
    run_interactive_to_fail(F_EQUAL, "", "intrs");
    run_interactive_to_fail(F_EQUAL, "", "intros p1 p2 p3 p4 p5 p6 bad_p");
    run_interactive_to_fail(
        "forall a b c d: ℤ, a < b -> c < d -> a + c < b + d",
        r#"
        intros a b c d a_lt_b c_lt_d
        "#,
        "add_hyp a b",
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
fn fail_instance_recovery() {
    let mut se = run_interactive(
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
    let e = se.run_tactic("apply lt_trans");
    if let Err(Error::CanNotFindInstance(e)) = e {
        assert_eq!(e.first_needed_wild(), 1);
        let tac = e.tactic_by_answer("b + c").unwrap();
        se.run_tactic(&tac).unwrap();
        return;
    }
    panic!("Expected to not finding instance");
}

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
fn sigma_1_n() {
    run_interactive_to_end(
        "∀ n: ℤ, 0 ≤ n -> 2 * sigma 0 (n+1) (λ i: ℤ, i) = n * (n + 1)",
        r#"
        apply simple_induction
        intros n n_pos gam_farz
        add_hyp (sigma 0 (n + 1) (λ i: ℤ, i) + sigma (n + 1) ((n + 1) + 1) (λ i: ℤ, i) = sigma 0 ((n + 1) + 1) (λ i: ℤ, i))
        apply sigma_plus
        rewrite <- H
        add_hyp (2 * (sigma 0 (n + 1) (λ x0: ℤ, x0) + sigma (n + 1) ((n + 1) + 1) (λ x0: ℤ, x0)) = n * (n + 1) + 2 * (n + 1))
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

#[test]
fn switch() {
    run_interactive_to_end(
        "∀ a: ℤ, ∃ b: ℤ, a < b",
        r#"
        intros a
        apply (ex_intro ? ? (a + 1))
        add_hyp (a = a+0)
        ring
        rewrite H
        add_hyp ((a+0)+1 = a+1)
        Switch 1
        rewrite H0
        apply lt_plus_l
        apply lt_0_1
        ring
        "#,
    );
    run_interactive_to_fail(
        "∀ a: ℤ, ∃ b: ℤ, a < b",
        r#"
        intros a
        "#,
        "Switch 1",
    );
}

#[test]
fn set_lemma() {
    run_interactive_to_end(
        "∀ T: U, ∀ a: T, ∀ S: set T, a ∈ S -> { a } ∪ (S ∖ { a }) = S",
        r#"
        intros T a S H
        apply minus_of_subset
        apply included_fold
        intros a2 a2_in_a
        apply (singleton_unfold ? ? ?) in a2_in_a
        rewrite <- a2_in_a
        apply H
    "#,
    );
}
#[test]
fn assumption_test() {
    run_interactive_to_end(
        "∀ P Q R S: U, (R -> S) -> R -> (S -> False) ∨ Q -> Q",
        r#"
        intros P Q R S H1 H2 H3
        assumption
    "#,
    );
}
#[test]
fn auto_set_test() {
    run_interactive_to_end(
        "∀ A: U, ∀ P Q R S: set A, ∀ a: A, (a ∈ R -> a ∈ S) -> a ∈ R -> ((a ∈ S -> False) ∨ a ∈ Q) -> a ∈ Q",
        r#"
        intros A P Q R S a H1 H2 H3
        auto_set
    "#,
    );
}
