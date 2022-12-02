use super::Result;
use crate::{
    analysis::{
        arith::{LinearPoly, Poly, Rati},
        big_fraction::BigFraction,
        logic::{LogicArena, LogicBuilder, LogicValue},
    },
    brain::{
        detect::{detect_r_ty, detect_z_ty},
        Term, TermRef,
    },
    interactive::Frame,
};

use minilp::{ComparisonOp, OptimizationDirection, Problem};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum CmpOp {
    Lt,
    Le,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RealIneq(Poly<BigFraction>, CmpOp);

fn convert_calculator_mode(
    term: TermRef,
    arena: LogicArena<'_, RealIneq>,
) -> LogicValue<'_, RealIneq> {
    let r = convert(term, arena);
    fn is_good(x: &LogicValue<'_, RealIneq>) -> bool {
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

fn poly_to_logic_value(poly: Poly<BigFraction>, op: CmpOp) -> LogicValue<'static, RealIneq> {
    if poly.variables().is_empty() {
        let is_correct = match op {
            CmpOp::Lt => poly.constant().clone() > 0.into(),
            CmpOp::Le => poly.constant().clone() >= 0.into(),
        };
        match is_correct {
            true => LogicValue::True,
            false => LogicValue::False,
        }
    } else {
        LogicValue::from(RealIneq(poly, op))
    }
}

fn is_zero_logic_value(
    poly: Poly<BigFraction>,
    arena: LogicArena<'_, RealIneq>,
) -> LogicValue<'_, RealIneq> {
    let mut result = LogicValue::False;
    for mut p in poly.decompose() {
        let l1 = poly_to_logic_value(p.clone(), CmpOp::Le);
        p.negate();
        let l2 = poly_to_logic_value(p, CmpOp::Le);
        result = result.or(l1.and(l2, arena), arena);
    }
    result
}

fn add_non_zero_conditions<'a>(
    mut core: LogicValue<'a, RealIneq>,
    arena: LogicArena<'a, RealIneq>,
    conditions: impl Iterator<Item = Poly<BigFraction>>,
) -> LogicValue<'a, RealIneq> {
    for c in conditions {
        let c_is_zero = is_zero_logic_value(c, arena);
        let c_is_not_zero = c_is_zero.clone().not(arena);
        // This one is nice. We need to replace a logic value with a equivalent one (with iff relation), to work in both goal
        // and hyp. So (precondition -> statement) is not correct (because in goal position, it always holds if precondition is
        // not true, but the original condition might not) and (precondition /\ statement) is not true as well (because in
        // hyp position, it will add a precondition to our knowledge which might be wrong). The solution used here is
        // (~ precondition /\ unknown \/ precondition /\ statement) which is iff of the original statement.
        core = c_is_zero
            .and(LogicValue::unknown(), arena)
            .or(c_is_not_zero.and(core, arena), arena)
    }
    core
}

fn convert(term: TermRef, arena: LogicArena<'_, RealIneq>) -> LogicValue<'_, RealIneq> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if detect_r_ty(ty) || detect_z_ty(ty) {
                        if unique_name == "eq" {
                            let (d, should_not_zeros) =
                                Rati::<BigFraction>::from_subtract(op2.clone(), op1.clone());
                            let Rati(ds, dm) = d;
                            return add_non_zero_conditions(
                                is_zero_logic_value(ds, arena)
                                    .or(is_zero_logic_value(dm, arena), arena),
                                arena,
                                should_not_zeros.into_iter(),
                            );
                        }
                        if unique_name == "lt" {
                            let (d, should_not_zeros) =
                                Rati::<BigFraction>::from_subtract(op2.clone(), op1.clone());
                            let Rati(d1s, d1m) = d;
                            let (mut d2s, mut d2m) = (d1s.clone(), d1m.clone());
                            d2s.negate();
                            d2m.negate();
                            let l1 = poly_to_logic_value(d1s, CmpOp::Lt);
                            let l2 = poly_to_logic_value(d1m, CmpOp::Lt);
                            let l3 = poly_to_logic_value(d2s, CmpOp::Lt);
                            let l4 = poly_to_logic_value(d2m, CmpOp::Lt);
                            return add_non_zero_conditions(
                                l1.and(l2, arena).or(l3.and(l4, arena), arena),
                                arena,
                                should_not_zeros.into_iter(),
                            );
                        }
                    }
                }
            }
        }
    }
    LogicValue::unknown()
}

fn check_contradiction_lp(
    var_cnt: usize,
    linear_polies: &[(LinearPoly<BigFraction>, CmpOp)],
) -> bool {
    let mut problem = Problem::new(OptimizationDirection::Maximize);
    let vars = (0..var_cnt)
        .map(|_| problem.add_var(1., (-f64::INFINITY, f64::INFINITY)))
        .collect::<Vec<_>>();
    for (poly, op) in linear_polies {
        let x = poly
            .variables()
            .iter()
            .map(|(x, c)| {
                let t = x.as_f64_safe()?;
                Some((vars[*c], t))
            })
            .collect::<Option<Vec<_>>>();
        let Some(x) = x else { continue };
        let Some(mut c) = poly.constant().as_f64_safe() else { continue };
        c *= -1.;
        if matches!(op, CmpOp::Lt) {
            c += 1e-7;
        }
        problem.add_constraint(&x, ComparisonOp::Ge, c)
    }
    matches!(problem.solve(), Err(minilp::Error::Infeasible))
}

fn check_contradiction(polies: &[RealIneq]) -> bool {
    let (var_cnt, linear_polies) = LinearPoly::from_slice(polies.iter().map(|x| x.0.clone()));
    let lp_with_op = linear_polies
        .into_iter()
        .zip(polies.iter().map(|x| x.1))
        .collect::<Vec<_>>();
    check_contradiction_lp(var_cnt, &lp_with_op)
}

fn negator(mut poly: RealIneq) -> RealIneq {
    poly.0.negate();
    poly.1 = match poly.1 {
        CmpOp::Lt => CmpOp::Le,
        CmpOp::Le => CmpOp::Lt,
    };
    poly
}

pub fn lra(frame: Frame) -> Result<Vec<Frame>> {
    let is_calculator = frame.engine.params.get("lra") == Some(&"calculator".to_string());
    LogicBuilder::build_tactic(
        "lra",
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
        run_interactive_to_end(goal, "intros\nlra");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "lra");
    }

    #[test]
    fn simple() {
        success("1. + 2. = 3.");
        success("0.5 + 0.5 = 1.");
        success("1 / 2 + 0.5 = 1.");
        success("0.5 * 0.5 = 0.25");
        fail("1. + 2. = 4.");
    }

    #[test]
    fn ring() {
        success("∀ x: ℝ, 0.5 * x + 0.5 * x = x");
    }

    #[test]
    fn lra_simple() {
        fail("∀ x: ℝ, x > 1.2");
        success("∀ x: ℝ, 0.5 * x > 3. -> x > 1.2 -> 0.6 * x > 3.");
        fail("∀ x: ℝ, 0.5 * x > 3. -> x > 1.2 -> 0.4 * x > 3.");
        success("∀ x: ℝ, x = 3. -> x < 3.01");
    }

    #[test]
    fn div_simple() {
        success("∀ a b: ℝ, b > 0. -> a / b > 2. -> a > 2. * b");
        success("∀ a b: ℤ, b > 0 -> a / b > 2. -> a > 2 * b");
        success("∀ a b: ℤ, ~ b * b = 0 -> (a * a) / (b * b) = 2. -> a * a = 2 * b * b");
    }

    #[test]
    fn div_by_zero_is_zero() {
        success("∀ a: ℝ, a / 0. = 0.");
        success("∀ a: ℤ, a / 0 = 0.");
        fail("∀ a: ℤ, a / 0 = 5.");
        fail("∀ a: ℤ, a / (a - a) = 5.");
    }

    #[test]
    fn div_catch_zero_err() {
        fail("∀ a b c d: ℝ, a / b + c / d = (a * d + b * c) / (b * d)");
        success("∀ a b c d: ℝ, ~ b = 0. -> ~ d = 0. -> a / b + c / d = (a * d + b * c) / (b * d)");
    }

    #[test]
    fn no_unneeded_div_zero_precondition() {
        success("∀ a b: ℝ, a / b = a / b");
        success("∀ a b c d: ℝ, (a / b) / (c / d) = (a * d) / (b * c)");
        success(
            "∀ x n: ℝ, ~ n = 0. -> (x - 1. / n) * (x - 1. / n) = x * x - 2. * x * (1. / n) + (1. / n) * (1. / n)",
        );
    }

    #[test]
    fn transitivity() {
        success("∀ a b c d: ℝ, a < b -> b < c -> c < d -> a < d");
        success("∀ a b c d: ℝ, a ≤ b -> b ≤ c -> c ≤ d -> a ≤ d");
        fail("∀ a b c d: ℝ, a ≤ b -> b ≤ c -> c ≤ d -> a < d");
        success("∀ a b c d: ℝ, a ≤ b -> b < c -> c ≤ d -> a < d");
    }

    #[test]
    fn catch_float_error() {
        for i in 0..20 {
            let x = "0".repeat(i);
            fail(&format!("∀ x: ℝ, 1{x}. * x < 5. -> 1{x}.{x}1 * x < 5."));
            fail(&format!("∀ x: ℝ, 1{x}0. * x < 5. -> 1{x}1. * x < 5."));
            fail(&format!("∀ x: ℝ, 0.{x}1 * x < 5. -> 0.{x}2 * x < 5."));
        }
    }

    #[test]
    fn calculator_mode() {
        with_params("lra=calculator", || {
            success("1. < 2.");
            success("0.1 + 0.2 = 0.3");
            fail("1 < 1");
            fail("0.1 + 0.2 = 0.30000000000000004");
            fail("∀ x: ℝ, 2. * x = 4. -> x = 2.");
            success("∀ x: ℝ, x + x = 2. * x");
        });
        success("∀ x: ℝ, 2. * x = 4. -> x = 2.");
    }
}
