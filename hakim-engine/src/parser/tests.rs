use crate::{
    engine::{
        tests::{build_engine, with_params, EngineLevel},
        Engine,
    },
    notation_list,
};

use std::{sync::mpsc, thread, time::Duration};

fn panic_after<T, F>(d: Duration, f: F) -> T
where
    T: Send + 'static,
    F: FnOnce() -> T,
    F: Send + 'static,
{
    let (done_tx, done_rx) = mpsc::channel();
    let handle = thread::spawn(move || {
        let val = f();
        done_tx.send(()).expect("Unable to send completion signal");
        val
    });

    match done_rx.recv_timeout(d) {
        Ok(_) => handle.join().expect("Thread panicked"),
        Err(_) => panic!("Thread took too long"),
    }
}

#[test]
fn notation_list_works() {
    panic_after(Duration::from_millis(1000), || {
        let r = notation_list();
        assert!(r.len() < 100);
        assert!(r.len() > 10);
    });
}

fn parse_pretty(exp: &str) {
    parse_not_pretty(exp, exp);
}

fn parse_not_pretty(exp: &str, pretty: &str) {
    let eng = build_engine(EngineLevel::Full);
    let exp_term = eng.parse_text(exp).unwrap();
    let exp_pretty = eng.pretty_print(&exp_term);
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
    parse_pretty("∀ x0 x1: Universe, x0 → x1");
}

#[test]
fn number_ops() {
    parse_pretty("∀ x0 x1 x2: ℤ, x0 < x1 → x0 + x2 < x1 + x2");
    parse_pretty("∀ x0 x1: ℤ, (x0 + x1) * (x0 + x1) < x0 * x0 + x1 * x1");
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
    with_params("disabled_binops=[=]", || {
        parse_pretty("eq ℤ 2 3");
    });
    parse_pretty("∃ x0: ℤ, x0 = x0 + x0");
}

#[test]
fn iff_loop() {
    with_params("disabled_binops=[↔]", || {
        parse_not_pretty("True ↔ False", "~ True ∧ (False → True)");
    });
    with_params("disabled_binops=[→]", || {
        parse_not_pretty("False → True", "∀ x: False, True");
    });
}

#[test]
fn iff_check() {
    parse_pretty("∀ x0 x1: ℤ, x0 = x1 ↔ x0 + 3 = x1 + 3");
    parse_pretty("∀ A B: Universe, A ↔ B → B ↔ A");
    parse_pretty("∀ A: Universe, A ↔ (A → A)");
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
    parse_pretty("∀ salam x2: ℤ, salam < x2");
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
    parse_error("∀");
    parse_error("∀ x");
    parse_error("∀ x:");
    parse_error("∀ x: ℤ");
    parse_error("∀ x: ℤ,");
    parse_error("∀ 2: 5");
    parse_error("∀ : 5 = 5");
    parse_error("{2: ℤ}");
    parse_error("forall x ℤ");
    parse_error("forall x -> ℤ");
}
#[test]
fn divid_and_mod() {
    parse_pretty("∀ a b: ℤ, a mod b | a");
}

#[test]
fn mod_in_name() {
    parse_pretty("∀ a b mod_a_b: ℤ, mod_a_b = a mod b");
    parse_pretty("∀ forall_x: ℤ, forall_x = forall_x");
}

#[test]
fn gt_le_ge() {
    parse_not_pretty("3 > 2", "2 < 3");
    parse_pretty("1 ≤ 5");
    parse_not_pretty("3 ≥ 2", "2 ≤ 3");
}

#[test]
fn abs_in_type_pos() {
    parse_pretty("∀ y: ∀ t: ℤ, t = t, y = y");
}

#[test]
fn len() {
    parse_pretty("|2|");
    parse_pretty("|- 2| * 5");
    parse_pretty("|{1, 2, 5}| = 3");
    parse_pretty("|{ x: ℤ | x = 2 * x }| = 3");
    parse_pretty("∀ f: ℤ → ℤ, |2| = f (|2|)");
    parse_pretty("∀ x: ℤ, x | |x|");
}

#[test]
fn chars() {
    parse_pretty("'a'");
    parse_pretty("{'a', 'b', 'c'}");
    parse_pretty("'('");
    parse_pretty("'!'");
    parse_pretty("'~'");
    parse_pretty("chr 0");
    parse_not_pretty("chr 97", "'a'");
    parse_not_pretty("chr 2096", "'0'");
    parse_error("'gav'");
    parse_error("''");
}

#[test]
fn strings() {
    parse_pretty(r#""salam""#);
    parse_pretty(r#"|""| = 0"#);
    parse_pretty(r#""salam" ++ "7""#);
}

#[test]
fn list() {
    parse_pretty("[] ++ [2, 3, 5]");
    parse_pretty("λ f: list ℤ → ℤ, f [2, 3, 5]");
}

#[test]
fn notation_curry() {
    parse_not_pretty("pow 2", "λ x: ℤ, 2 ^ x");
    parse_not_pretty("len1 ℤ", "λ x: ℤ, |x|");
}

#[test]
fn hidden_args() {
    parse_pretty(r#"cnt 'a' "salam""#);
}

#[test]
fn sigma() {
    parse_not_pretty("λ f: ℤ → ℤ, sigma 0 5 f", "λ f: ℤ → ℤ, Σ x in [0, 5) f x");
    parse_pretty("Σ x in [0, 5) x * x");
    parse_pretty("Σ i in [0, 5) 12");
}

#[test]
fn in_in_name() {
    parse_pretty("λ include: ℤ → ℤ, include 5");
    parse_pretty("included_fold");
}

#[test]
fn tuples() {
    parse_error("()");
    parse_pretty("(1, 2, 3)");
}

#[test]
fn max_width() {
    parse_pretty(
        r#"∀ a b n: ℤ,
  (Σ i in [0 + 1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1)) + a ^ (n + 1)
    + ((Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1))
        + b ^ (n - 0 + 1))
    = (Σ i in [1, n + 1) cm n (i - 1) * a ^ i * b ^ (n - i + 1))
        + ((Σ i0 in [1, n + 1) cm n i0 * a ^ i0 * b ^ (n - i0 + 1))
            + a ^ (n + 1)
            + b ^ (n - 0 + 1))"#,
    );
    parse_pretty(
        r#"∀ k: ℤ,
  ∀ P: ℤ → Universe,
    (∀ n: ℤ, k ≤ n → (∀ m: ℤ, k ≤ m → m < n → P m) → P n) → ∀ n: ℤ, k ≤ n → P n"#,
    );
}
