use crate::{
    brain::infer::{match_and_infer, InferResults},
    engine::Engine,
};

use super::{infer::type_of_and_infer, type_of};

fn wild_need_local(exp: &str) {
    let eng = Engine::default();
    let (term, cnt) = eng.parse_text_with_wild(exp).unwrap();
    let mut infers = InferResults::new(cnt);
    let ty = match type_of_and_infer(term.clone(), &mut infers) {
        Ok(x) => x,
        Err(e) if matches!(e.reason, super::ErrorReason::WildNeedLocalVar(_)) => return,
        Err(e) => panic!("Expected WildNeedLocalVar error but got {:?}", e),
    };
    match type_of_and_infer(ty.clone(), &mut infers) {
        Ok(x) => panic!(
            "There should be a wild bound to a local, but nothing found\n\
        exp: {:?}\nexp filled: {:?}\nty: {:?}\n ty of ty: {:?}",
            term.clone(),
            infers.fill(term),
            ty,
            x
        ),
        Err(e) if matches!(e.reason, super::ErrorReason::WildNeedLocalVar(_)) => (),
        Err(e) => panic!("Expected WildNeedLocalVar error but got {:?}", e),
    }
}

fn check_type(exp: &str, ty: &str) {
    let eng = Engine::default();
    let exp_term = eng.parse_text(exp).unwrap();
    let ty_term = eng.parse_text(ty).unwrap();
    assert_eq!(type_of(exp_term).unwrap(), ty_term);
}

fn fail_type(exp: &str) {
    let eng = Engine::default();
    let exp_term = eng.parse_text(exp);
    if let Ok(t) = exp_term {
        panic!("We expect fail but type {:?} found for {}", t, exp)
    }
}

fn fail_match_infer(a: &str, b: &str) {
    let eng = Engine::default();
    let (a, c1) = eng.parse_text_with_wild(a).unwrap();
    let (b, c2) = eng.parse_text_with_wild(b).unwrap();
    let c = std::cmp::max(c1, c2);
    if match_and_infer(a, b, &mut InferResults::new(c)).is_ok() {
        panic!("We expect fail but it found match")
    }
}

#[test]
fn number_z() {
    check_type("2", "ℤ");
    check_type("2 + 5", "ℤ");
    check_type("2 + (2 * 3 + 1) * 6", "ℤ");
}

#[test]
fn lambda_simple() {
    check_type("λ x: ℤ, x + 2", "ℤ → ℤ");
}

#[test]
fn lambda2() {
    check_type("λ x y: ℤ, x + y", "ℤ → ℤ → ℤ");
}

#[test]
fn lambda_dependent() {
    check_type("λ A: U, λ x: A, x", "∀ A: U, A → A");
}

#[test]
fn forall_bad_ty() {
    fail_type("∀ A: U, 2");
    fail_type("∀ A: 2, U");
    fail_type("∀ x: ℤ, x + 2");
}

#[test]
fn lambda_bad_ty() {
    check_type("λ A: U, 2", "U → ℤ");
    fail_type("λ A: 2, U");
    check_type("λ A: U, U", "U → Universe1");
}

#[test]
fn forall_universe() {
    check_type("ℤ → ℤ → ℤ", "U");
    check_type("∀ x: ℤ, x + 2 < 7", "U");
    check_type("∀ A: U, A → A", "Universe1");
}

#[test]
fn exists_good() {
    check_type("exists x: ℤ, x < 2", "U");
    check_type("exists x y: ℤ, x < y", "U");
    check_type("exists x: ℤ, x < x -> exists x: ℤ, 2 * x < x", "U");
}

#[test]
fn exists_bad() {
    fail_type("exists x: 2, x");
    fail_type("exists x: ℤ, x");
    fail_type("exists x: ℤ, x + 2");
    fail_type("exists x: U, x");
}

#[test]
fn infer_stack_overflow() {
    fail_match_infer(
        "?x -> ?x -> ?x -> ?x",
        "(?a → ?b) → ((?b → ?c) → (?a → ?c))",
    );
}

#[test]
fn iff_fail() {
    check_type(
        "∀ A: U, ∀ x y: set A, ∀ a: A, a ∈ x ∪ y ↔ a ∈ x ∨ a ∈ y",
        "Universe1",
    );
}

#[test]
fn local_wild() {
    wild_need_local("∀ f: Universe1 -> U, ?x ∧ f ∀ T: U, ∀ a b: T, eq ?x a b");
    check_type("∀ T: U, ∀ a b: T, eq ?x a b -> eq ?x b a", "Universe1");
}

#[test]
fn fn_app() {
    check_type(
        "∀ A B: Universe, ∀ f: A -> B, ∀ g: B -> Universe, ∀ x: A, g (f x)",
        "Universe1",
    );
}

#[test]
fn eq_explicit() {
    check_type(
        "∀ x0: U, ∀ x1: U, ∀ x2: x0 → x1, ∀ x3: x0, ∀ x4: x0, eq x0 x3 x4 → eq x1 (x2 x3) (x2 x4)",
        "Universe1",
    );
}

#[test]
fn tuples() {
    check_type("(1, 2, 3)", "ℤ ∧ ℤ ∧ ℤ");
    check_type("((1, 2), 3)", "(ℤ ∧ ℤ) ∧ ℤ");
    check_type("([1, 2], 3)", "list ℤ ∧ ℤ");
}
