use crate::engine::Engine;

fn parse_pretty(exp: &str) {
    let mut eng = Engine::default();
    eng.add_axiom("tmp_axiom", exp).unwrap();
    let ty = eng.calc_type("tmp_axiom").unwrap();
    let pretty = format!("{:?}", ty);
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
}
