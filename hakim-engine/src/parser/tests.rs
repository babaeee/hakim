use crate::engine::Engine;

fn parse_pretty(exp: &str) {
    let eng = Engine::default();
    let exp_term = eng.parse_text(exp).unwrap();
    let pretty = format!("{:?}", exp_term);
    assert_eq!(exp, pretty);
}

#[test]
fn simple_forall() {
    parse_pretty("∀ x0: U, x0");
}

#[test]
fn forall_arrow() {
    parse_pretty("∀ x0: U, ∀ x1: U, x0 → x1");
}

#[test]
fn number_ops() {
    parse_pretty("∀ x0: ℤ, ∀ x1: ℤ, ∀ x2: ℤ, x0 < x1 → x0 + x2 < x1 + x2");
    parse_pretty("∀ x0: ℤ, ∀ x1: ℤ, (x0 + x1) * (x0 + x1) < x0 * x0 + x1 * x1");
    parse_pretty("1 + 2 * 3 * 4 + 5 * 6 < 7 + 8 * 9");
    parse_pretty("(1 * 2 + 3 * 4) * (1 * 2 + 3 * 4)");
}

#[test]
fn bigint() {
    parse_pretty("1 < 100000000000000000000000");
}

#[test]
fn simple_fun() {
    parse_pretty("λ x0: ℤ, x0 + 2");
    parse_pretty("(λ x0: ℤ, 3 * x0 + 2) 7");
    // Paranthesis around second function is not neccessary, but it helps clearness
    // and coq does it, so don't remove it
    parse_pretty("(λ x0: ℤ, x0) 7 (λ x0: ℤ, 3 * x0 + 2)");
}

#[test]
fn simple_exists() {
    parse_pretty("∃ x0: ℤ, x0 < 2");
    parse_pretty("(∃ x0: ℤ, x0 < 2) → ∃ x0: ℤ, x0 < 2");
    parse_pretty("∃ x0: ℤ, x0 < 2 → ∃ x1: ℤ, x1 < x0");
}

#[test]
fn universes() {
    parse_pretty("U");
    parse_pretty("U1");
    parse_pretty("U2");
    parse_pretty("U3");
    parse_pretty("U → U1");
    parse_pretty("U3 → U2");
}

#[test]
fn and_or_not() {
    parse_pretty("∃ x0: ℤ, x0 < 2 ∨ 5 < x0 ∧ x0 < 7");
}

#[test]
fn eq() {
    parse_pretty("2 = 3");
    parse_pretty("∃ x0: ℤ, x0 = x0 + x0");
}

#[test]
fn iff_check() {
    parse_pretty("∀ x0: ℤ, ∀ x1: ℤ, x0 = x1 ↔ x0 + 3 = x1 + 3");
}

#[test]
fn sets() {
    parse_pretty("{ x0: ℤ | x0 < 5 }");
    parse_pretty("2 ∈ { x0: ℤ | x0 < 5 }");
    parse_pretty("{ x0: ℤ | 5 < x0 } ∩ { x0: ℤ | x0 < 10 }");
    parse_pretty("{2} ∩ {}");
    parse_pretty("{1, 2, 3}");
}
