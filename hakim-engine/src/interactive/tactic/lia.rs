use num_bigint::{BigInt, Sign};

use super::Result;
use crate::{
    analysis::{
        arith::{ConstRepr, LinearPoly, Poly},
        logic::{LogicArena, LogicBuilder, LogicValue},
    },
    brain::{
        detect::{detect_len, detect_z_ty},
        Term, TermRef,
    },
    interactive::Frame,
    parser::BinOp,
    term_ref,
};

use minilp::{ComparisonOp, OptimizationDirection, Problem};

fn convert_calculator_mode(
    term: TermRef,
    arena: LogicArena<'_, Poly<BigInt>>,
) -> LogicValue<'_, Poly<BigInt>> {
    let r = convert(term, arena);
    fn is_good(x: &LogicValue<'_, Poly<BigInt>>) -> bool {
        match x {
            LogicValue::Exp(_) => false,
            LogicValue::True | LogicValue::False => true,
        }
    }
    if is_good(&r) {
        r
    } else {
        LogicValue::unknown()
    }
}

fn convert(term: TermRef, arena: LogicArena<'_, Poly<BigInt>>) -> LogicValue<'_, Poly<BigInt>> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if detect_z_ty(ty) {
                        if unique_name == "eq" {
                            let mut d1 = Poly::<BigInt>::from_subtract(op2.clone(), op1.clone());
                            if d1.is_zero() {
                                return LogicValue::True;
                            }
                            if d1.variables().is_empty() {
                                return LogicValue::False;
                            }
                            d1.add(1.into());
                            let mut d2 = Poly::<BigInt>::from_subtract(op1.clone(), op2.clone());
                            d2.add(1.into());
                            let l1 = LogicValue::from(d1);
                            let l2 = LogicValue::from(d2);
                            return l1.and(l2, arena);
                        }
                        if unique_name == "lt" {
                            let d = Poly::<BigInt>::from_subtract(op2.clone(), op1.clone());
                            if d.variables().is_empty() {
                                return if *d.constant() > 0i32.into() {
                                    LogicValue::True
                                } else {
                                    LogicValue::False
                                };
                            }
                            return LogicValue::from(d);
                        }
                    }
                }
            }
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "divide" {
                    if let (Some(a), Some(b)) = (BigInt::from_term(op1), BigInt::from_term(op2)) {
                        if b == BigInt::from(0) || (b % a) == BigInt::from(0) {
                            return LogicValue::True;
                        }
                        return LogicValue::False;
                    }
                }
            }
        }
    }
    LogicValue::unknown()
}

fn inject_conditions(polies: Vec<Poly<BigInt>>) -> Vec<Poly<BigInt>> {
    let m1 = -1;
    let m1 = term_ref!(n m1);
    let div_mods = polies
        .iter()
        .flat_map(|x| x.variables().iter().flat_map(|x| x.1.iter()))
        .flat_map(|x| {
            if let Some((ty, _)) = detect_len(x) {
                return match ty.as_ref() {
                    Term::App { func, op: _ } => match func.as_ref() {
                        Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                            "list" => vec![Poly::<BigInt>::from_subtract(x.clone(), m1.clone())],
                            _ => vec![],
                        },
                        _ => vec![],
                    },
                    _ => vec![],
                }
                .into_iter();
            }
            if let Some((_, BinOp::ModOf, b)) = BinOp::detect(x) {
                if let Term::Number { value: bval } = b.as_ref() {
                    if bval.sign() == Sign::Plus {
                        return vec![
                            Poly::<BigInt>::from_subtract(b, x.clone()),
                            Poly::<BigInt>::from_subtract(x.clone(), m1.clone()),
                        ]
                        .into_iter();
                    }
                }
            }
            vec![].into_iter()
        })
        .collect();
    [div_mods, polies].concat()
}

fn check_contradiction_lp(var_cnt: usize, linear_polies: &[LinearPoly<BigInt>]) -> bool {
    let bounded = |v, minmax| {
        let mut problem = Problem::new(OptimizationDirection::Maximize);
        let vars = (0..var_cnt)
            .map(|x| {
                problem.add_var(
                    if x == v { minmax } else { 0. },
                    (-f64::INFINITY, f64::INFINITY),
                )
            })
            .collect::<Vec<_>>();
        for poly in linear_polies {
            let x = poly
                .variables()
                .iter()
                .map(|(x, c)| {
                    let t: i32 = x.try_into().ok()?;
                    Some((vars[*c], f64::from(t)))
                })
                .collect::<Option<Vec<_>>>();
            let x = match x {
                Some(x) => x,
                None => continue,
            };
            let c: i32 = match poly.constant().try_into() {
                Ok(x) => x,
                Err(_) => continue,
            };
            let c = -c + 1;
            problem.add_constraint(&x, ComparisonOp::Ge, f64::from(c))
        }
        match problem.solve() {
            Ok(x) => Some(x[vars[v]]),
            Err(minilp::Error::Infeasible) => None,
            Err(_) => Some(minmax * f64::INFINITY),
        }
    };
    for i in 0..var_cnt {
        let lb = bounded(i, -1.);
        let ub = bounded(i, 1.);
        match (lb, ub) {
            (Some(lb), Some(ub)) => {
                if lb.ceil() > ub.floor() {
                    return true;
                }
            }
            _ => return true,
        }
    }
    false
}

fn check_contradiction(polies: &[Poly<BigInt>]) -> bool {
    let polies = &inject_conditions(polies.to_vec());
    let (var_cnt, linear_polies) = LinearPoly::from_slice(polies.iter().cloned());
    check_contradiction_lp(var_cnt, &linear_polies)
}

fn negator(mut poly: Poly<BigInt>) -> Poly<BigInt> {
    poly.negate();
    poly.add(1.into());
    poly
}

pub fn lia(frame: Frame) -> Result<Vec<Frame>> {
    let is_calculator = frame.engine.params.get("lia") == Some(&"calculator".to_string());
    LogicBuilder::build_tactic(
        "lia",
        frame,
        if is_calculator {
            convert_calculator_mode
        } else {
            convert
        },
        check_contradiction,
        negator,
    )
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail, with_params};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nlia");
        run_interactive_to_end(goal, "intros\nz3");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "lia");
        run_interactive_to_fail(goal, "intros", "z3");
    }

    #[test]
    fn success_lia_goal() {
        run_interactive_to_end("forall x: ℤ, x < x + 1", "intros\nlia");
    }

    #[test]
    fn success_lia_one_var() {
        success("forall x: ℤ, 2 * x < 5 -> 6 * x < 10 + 2 * x");
    }

    #[test]
    fn unused_var() {
        success("forall x y: ℤ, y = 2 -> y + 2 = 4");
        fail("forall x y: ℤ, y = 2 -> y + 2 = 5");
    }

    #[test]
    fn lia_and_logic_simple() {
        success("forall x: ℤ, x < 5 ∨ x < 10 -> x < 20");
        fail("forall x: ℤ, x < 5 ∨ x < 100 -> x < 20");
        success("forall x: ℤ, x < 5 ∧ x < 100 -> x < 20");
        success("forall x: ℤ, x < 4 -> x < 20 ∧ (x < 100 ∨ x < 3) ∧ x < 6");
        success("forall x: ℤ, x < 4 -> x < 20 ∧ x < 100 ∨ x < 3 ∧ x < 6");
        fail("forall x: ℤ, x < 4 -> x < 20 ∧ (x < 100 ∨ x < 6) ∧ x < 3");
        success("forall x: ℤ, x = 1 ∨ x = 2 ∨ x = 3 -> x < 4 ∧ 0 < x ∧ (x = 3 ∨ x < 3)");
    }

    #[test]
    fn lia_equality() {
        success("forall x: ℤ, x = 3 ∨ x = 4 -> x < 5");
        success("forall x: ℤ, 3 < x ∧ x < 5 -> x = 4");
        success("forall x: ℤ, 0 < x + 1 -> x = 0 ∨ 0 < x");
        success("forall x: ℤ, 0 < x ∨ 0 = x ∨ x < 0");
        fail("forall x: ℤ, 0 < x ∨ x < 0");
        success("forall x y: ℤ, (x < 10 -> y = 2) -> x = 5 -> y = 2");
        fail("forall x y: ℤ, (x = 5 -> y = 2) -> x < 10 -> y = 2");
    }

    #[test]
    fn success_lia_use_integer() {
        success("forall x: ℤ, 4 < 2 * x -> 5 < 2 * x");
        success("forall x: ℤ, 2 * x < 6 -> 2 * x < 5");
    }

    #[test]
    fn big_integer() {
        fail("∀ x: ℤ, 10000000000000000000000000000000000000000001 * x = 10000000000000000000000000000000000000000000");
    }

    #[test]
    fn logic_unknown() {
        success("∀ P: U, 2 = 2 ∨ P");
        fail("∀ P: U, 2 = 2 ∧ P");
        success("∀ P: U, forall x: ℤ, 2 * x < 6 ∧ P -> 2 * x < 5");
        fail("∀ P: U, forall x: ℤ, 2 * x < 6 ∨ P -> 2 * x < 5");
        success("∀ P: U, forall x: ℤ, 2 * x < 6 -> 2 * x < 5 ∨ P");
        fail("∀ P: U, forall x: ℤ, 2 * x < 6 -> 2 * x < 5 ∧ P");
    }

    #[test]
    fn number_unknown() {
        success("∀ f: (ℤ -> ℤ) -> (ℤ -> ℤ), 2 * f (λ i: ℤ, i + 5) 2 = f (λ i: ℤ, i + 5) 2 + f (λ i: ℤ, i + 5) 2");
        fail("∀ f: (ℤ -> ℤ) -> (ℤ -> ℤ), 2 = f (λ i: ℤ, i + 5) 2");
    }

    #[test]
    fn fail_simple() {
        fail("forall x: ℤ, 2 < x");
    }

    #[test]
    fn fail_tight() {
        fail("forall x: ℤ, 5 < 2 * x -> 6 < 2 * x");
    }

    #[test]
    fn success_lia_hyp() {
        run_interactive_to_end("forall x: ℤ, x + 2 < x + 1 -> False", "intros\nlia");
    }

    #[test]
    fn div_mod() {
        success("∀ a, a mod 2 = 0 ∨ a mod 2 = 1");
        fail("∀ a, a mod 2 = 1");
        fail("∀ a, a mod 2 = 0");
        success("∀ a, a mod 2 = 2 -> False");
        fail("2 mod 4 = 3");
    }

    #[test]
    fn sigma_simple() {
        success("∀ n: ℤ, sigma 0 (n + 1 + 1) (λ i: ℤ, i) = sigma 0 (n + 1) (λ i: ℤ, i) + n + 1");
        fail("∀ n: ℤ, sigma 0 (n + 1 + 1) (λ i: ℤ, i) = sigma 0 (n + 1) (λ i: ℤ, i) + n");
        success("sigma (-2) (4) (λ i: ℤ, i * i) = 19");
        success("sigma 2 4 (λ i: ℤ, i * i) = 13");
        success("2 * sigma 0 (0 + 1) (λ i: ℤ, i) = 0 * (0 + 1)");
    }

    #[test]
    fn sigma_factor() {
        success("∀ n, (Σ i in [0, n) 1) = n");
        run_interactive_to_end(
            "∀ n: ℤ, 0 ≤ n → (Σ i in [0, n) 2 * i + 1) = n * n",
            r#"
            intros
            replace #1 ((Σ i in [0, n) 2 * i + 1)) with (2 * (Σ i in [0, n) i) + n)
            z3
            add_from_lib sigma_0_n
            add_hyp sigma_0_n_ex := (sigma_0_n (n))
            rewrite sigma_0_n_ex
            add_from_lib cm2
            add_hyp cm2_ex := (cm2 (n))
            z3
        "#,
        )
    }

    #[test]
    fn sigma_hard() {
        success("∀ n: ℤ, 0 ≤ n → sigma 0 n (λ i: ℤ, 2 * i + 1) = n * n → sigma 0 (n + 1) (λ i: ℤ, 2 * i + 1) = (n + 1) * (n + 1)");
    }

    #[test]
    fn transitivity() {
        success("∀ a b c d: ℤ, a < b -> b < c -> c < d -> a < d");
        success("∀ a b c d: ℤ, a ≤ b -> b ≤ c -> c ≤ d -> a ≤ d");
        fail("∀ a b c d: ℤ, a ≤ b -> b ≤ c -> c ≤ d -> a < d");
        success("∀ a b c d: ℤ, a ≤ b -> b < c -> c ≤ d -> a < d");
    }

    #[test]
    #[ignore]
    fn pow_simple() {
        success("∀ n: ℤ, n ^ 2 = n * n");
        fail("∀ n: ℤ, 2 * 2 ^ n = 2 ^ (n+1)"); // wrong for n = -1
        fail("∀ n: ℤ, 0 ^ n = 0"); // wrong for n = 0
        success("∀ n: ℤ, 1 ^ n = 1"); // correct, even for n <= 0
        success("0 ^ 1 = 0");
        success("1 ^ 0 = 1");
        success("1 ^ (- 2) = 1");
        success("∀ n: ℤ, n ^ 1 = n");
        //success("∀ n: ℤ, ~ n = 0 -> n ^ 0 = 1");
    }

    #[test]
    fn very_huge_variables() {
        use std::fmt::{Error, Write};
        (|| -> Result<(), Error> {
            let mut s = String::new();
            write!(s, "∀ x y ")?;
            let t = 30;
            for i in 1..=t {
                write!(s, "a{i} ")?;
            }
            write!(s, ": ℤ, a1 = 1 -> ")?;
            for i in 2..=t {
                write!(s, "a{} = a{} * 1000 -> ", i, i - 1)?;
            }
            write!(s, "x = a{t} -> y = a{t} + 1 -> x = y")?;
            fail(&s);
            Ok(())
        })()
        .unwrap();
    }

    #[test]
    #[ignore = "z3 is broken"]
    fn calculator_mode() {
        with_params("lia=calculator", || {
            success("1 < 2");
            success("2 + 2 = 4");
            fail("1 < 1");
            fail("2 < 1");
            success("-1000000000000000000 < 1");
            fail("∀ x: ℤ, 2 * x = 4 -> x = 2");
            success("∀ x: ℤ, x + x = 2 * x");
        });
        success("∀ x: ℤ, 2 * x = 4 -> x = 2");
    }

    #[test]
    #[ignore = "z3 is broken"]
    fn lists() {
        success(r#" ∀ l, |l| < |l + "x"| "#);
        success(r#" ∀ l, cnt 'x' l + 1 = cnt 'x' (l + "x") "#);
        success(r#" ∀ l, cnt 'y' l = cnt 'y' (l + "x") "#);
        fail(r#" ∀ A: U, ∀ a b: list A, |a| < |a + b| "#);
        success(r#" ∀ A: U, ∀ a b: list A, |a| ≤ |a + b| "#);
        success(r#"|[1, 2, 3]| = 3"#);
        fail(r#"[1] + [2] = [2] + [1]"#);
    }

    #[test]
    #[ignore = "z3 is broken"]
    fn sets() {
        success(r#"|set_empty ℤ| = 0"#);
    }

    #[test]
    fn reals() {
        fail("1 / 2 = 1 / 3");
    }

    #[test]
    #[ignore = "z3 is broken"]
    fn tuples() {
        success("(1, 2, 3, 4) = (1, 1 + 1, 1 + 1 + 1, 1 + 1 + 1 + 1)");
        fail("(1, 2, 3, 4, 5) = (1, 2, 4, 4, 5)");
        success("0 ≤ 0 ∧ ((3 * 0 + 2, 0) = (0 + 1, 0) ∨ (3 * 0 + 2, 0) = (0 + 2, 0))");
    }

    #[test]
    fn divide_calculte() {
        success("2 | 10000");
        fail("2 | 1");
        success("2 | 0")
    }
}
