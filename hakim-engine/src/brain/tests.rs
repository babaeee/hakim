use crate::engine::Engine;

use super::type_of;

fn check_type(exp: &str, ty: &str) {
    let eng = Engine::default();
    let exp_term = eng.parse_text(exp).unwrap();
    let ty_term = eng.parse_text(ty).unwrap();
    assert_eq!(type_of(exp_term).unwrap(), ty_term);
}

fn fail_type(exp: &str) {
    let eng = Engine::default();
    let exp_term = eng.parse_text(exp).unwrap();
    match type_of(exp_term) {
        Ok(t) => panic!("We expect fail but type {:?} found for {}", t, exp),
        Err(_) => (),
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
