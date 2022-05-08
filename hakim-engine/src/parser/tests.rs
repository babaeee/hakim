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
    parse_pretty("∀ x0: Universe, x0");
}

#[test]
fn forall_arrow() {
    parse_pretty("∀ x0: Universe, ∀ x1: Universe, x0 → x1");
}

#[test]
fn number_ops() {
    parse_pretty("∀ x0: ℤ, ∀ x1: ℤ, ∀ x2: ℤ, x0 < x1 → x0 + x2 < x1 + x2");
    parse_pretty("∀ x0: ℤ, ∀ x1: ℤ, (x0 + x1) * (x0 + x1) < x0 * x0 + x1 * x1");
    parse_pretty("1 + 2 * 3 * 4 + 5 * 6 < 7 + 8 * 9");
    parse_pretty("(1 * 2 + 3 * 4) * (1 * 2 + 3 * 4)");
    parse_pretty("3 * 2 ^ 5 + 4 = 100");
    parse_pretty("~ (3 * 2) ^ (5 + 4) = 100");
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
    parse_pretty("(λ x0: ℤ, λ x1: ℤ → ℤ, x0) 7 (λ x0: ℤ, 3 * x0 + 2)");
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
    parse_pretty("Universe");
    parse_pretty("Universe1");
    parse_pretty("Universe2");
    parse_pretty("Universe3");
    parse_pretty("Universe → Universe1");
    parse_pretty("Universe3 → Universe2");
}

#[test]
fn uniop() {
    parse_pretty("~ 2 = 3");
    parse_pretty("~ - 2 = 3");
    parse_pretty("- (2 + 3)");
    parse_pretty("- 2 + 3");
    parse_pretty("- - - (- 2 + 3)");
    parse_pretty("~ - 2 < - - 5");
    parse_pretty("2 * - (3 + 5)");
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
    parse_pretty("{ x0: set (2 | 3) | x0 ∈ {x0} }");
    // TODO: parse_pretty("{ x0: (2 | 3) | x0 = x0 }");
}

#[test]
fn sets() {
    parse_pretty("2 ∈ { x0: ℤ | x0 < 5 }");
    parse_pretty("{ x0: ℤ | 5 < x0 } ∩ { x0: ℤ | x0 < 10 }");
    parse_pretty("{2} ∩ {}");
    parse_pretty("{1, 2, 3}");
    parse_not_pretty("set_from_func ℤ (lt 5)", "{ x: ℤ | 5 < x }");
}

#[test]
fn set_and_app() {
    parse_pretty("∀ f: set ℤ → Universe, f {}");
    parse_pretty("∀ f: set ℤ → Universe, f {1, 2, 3}");
    parse_pretty("∀ f: set ℤ → Universe, ∀ X: set ℤ, f {1, 2, 3} → f X → X = {1, 2, 3}");
}

#[test]
fn pretty_names() {
    parse_pretty("∀ salam: ℤ, ∀ x2: ℤ, salam < x2");
    parse_not_pretty(
        "∀ x: Universe, x → ∀ x: ℤ, x < x",
        "∀ x: Universe, x → ∀ x0: ℤ, x0 < x0",
    );
}

#[test]
fn abstr_infer() {
    parse_not_pretty("∃ x, 2 < x", "∃ x: ℤ, 2 < x");
    parse_not_pretty("∀ x, 2 = x", "∀ x: ℤ, 2 = x");
    parse_not_pretty("∀ x, 2 = x", "∀ x: ℤ, 2 = x");
    parse_not_pretty("{ x | 5 < x }", "{ x: ℤ | 5 < x }");
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

#[test]
fn gt_le_ge() {
    parse_not_pretty("3 > 2", "2 < 3");
    parse_pretty("1 ≤ 5");
    parse_not_pretty("3 ≥ 2", "2 ≤ 3");
}
