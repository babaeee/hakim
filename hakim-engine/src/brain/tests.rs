use crate::{
    brain::infer::{match_and_infer, InferResults},
    engine::Engine,
};

use super::{infer::type_of_and_infer, type_of, Error};

fn wild_need_local(exp: &str) {
    let eng = Engine::default();
    let (term, cnt) = eng.parse_text_with_wild(exp).unwrap();
    let mut infers = InferResults::new(cnt);
    let ty = match type_of_and_infer(term.clone(), &mut infers) {
        Ok(x) => x,
        Err(Error::WildNeedLocalVar(_)) => return,
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
        Err(Error::WildNeedLocalVar(_)) => (),
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
    let exp_term = eng.parse_text(exp).unwrap();
    if let Ok(t) = type_of(exp_term) {
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
    check_type("λ A: U, U", "U → U1");
}

#[test]
fn forall_universe() {
    check_type("ℤ → ℤ → ℤ", "U");
    check_type("∀ x: ℤ, x + 2 < 7", "U");
    check_type("∀ A: U, A → A", "U1");
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
        "U1",
    );
}

#[test]
fn local_wild() {
    wild_need_local("∀ f: U1 -> U, ?x ∧ f ∀ T: U, ∀ a b: T, eq ?x a b");
    check_type("∀ T: U, ∀ a b: T, eq ?x a b -> eq ?x b a", "U1");
}
