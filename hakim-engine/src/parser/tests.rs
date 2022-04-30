use crate::engine::Engine;

fn parse_pretty(exp: &str) {
    parse_not_pretty(exp, exp);
}

fn parse_not_pretty(exp: &str, pretty: &str) {
    let eng = Engine::default();
    let exp_term = eng.parse_text(exp).unwrap();
    let exp_pretty = format!("{:?}", exp_term);
    assert_eq!(exp_pretty, pretty);
}

fn parse_error(exp: &str) {
    let eng = Engine::default();
    if eng.parse_text(exp).is_ok() {
        panic!("test passed unexpectedly")
    }
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
fn minus_prec() {
    parse_pretty("1 - 2");
    parse_pretty("1 - 2 - 3");
    parse_pretty("1 - 2 - 3 - 4");
    parse_pretty("1 - (2 - 3) - 4");
    parse_pretty("1 - (2 + 3) - 4");
    parse_pretty("1 - (2 + 3)");
    parse_pretty("1 - 2 + 3");
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
fn exists_raw() {
    parse_not_pretty("ex ℤ (lt 5)", "∃ x: ℤ, 5 < x");
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
fn set_and_divide() {
    parse_pretty("{ x0: ℤ | x0 < 5 }");
    parse_pretty("{ x0: set (2 | 3) | x0 < 5 }");
    // TODO: parse_pretty("{ x0: (2 | 3) | x0 < 5 }");
}

#[test]
fn sets() {
    parse_pretty("2 ∈ { x0: ℤ | x0 < 5 }");
    parse_pretty("{ x0: ℤ | 5 < x0 } ∩ { x0: ℤ | x0 < 10 }");
    parse_pretty("{2} ∩ {}");
    parse_pretty("{1, 2, 3}");
}

#[test]
fn set_and_app() {
    parse_pretty("∀ f: set ℤ → U, f {}");
    parse_pretty("∀ f: set ℤ → U, f {1, 2, 3}");
    parse_pretty("∀ f: set ℤ → U, ∀ X: set ℤ, f {1, 2, 3} → f X → X = {1, 2, 3}");
}

#[test]
fn pretty_names() {
    parse_pretty("∀ salam: ℤ, ∀ x2: ℤ, salam < x2");
    parse_not_pretty("∀ x: U, x → ∀ x: ℤ, x < x", "∀ x: U, x → ∀ x0: ℤ, x0 < x0");
}

#[test]
fn abstr_prec() {
    parse_pretty("(∃ x: ℤ, 2 < x) → 2 | 5");
    parse_pretty("∃ x: ℤ, 2 < x → 2 | 5");
}

#[test]
fn basic_fails() {
    parse_error("(2+3");
    parse_error("()");
    parse_error("(2+)+3");
    parse_error("forall");
    parse_error("forall x");
    parse_error("forall x:");
    parse_error("forall x: ℤ");
    parse_error("forall x: ℤ,");
    parse_error("forall 2: 5");
    parse_error("{2: ℤ}");
    parse_error("forall x ℤ");
    parse_error("forall x -> ℤ");
}
#[test]
fn divid_and_mod() {
    parse_pretty("∀ a: ℤ, ∀ b: ℤ, a mod b | a");
}
