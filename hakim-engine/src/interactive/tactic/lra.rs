use std::cmp::Ordering;

use super::Result;
use crate::{
    analysis::{
        arith::{ConstRepr, LinearPoly, Poly},
        logic::{LogicArena, LogicBuilder, LogicValue},
    },
    brain::{detect::detect_r_ty, Term, TermRef},
    interactive::Frame,
};

use minilp::{ComparisonOp, OptimizationDirection, Problem};
use num_bigint::BigInt;

#[derive(Debug, Clone)]
struct BigFraction {
    soorat: BigInt,
    makhraj: BigInt,
}

impl BigFraction {
    fn is_negative(&self) -> bool {
        (self.soorat < 0i32.into()) ^ (self.makhraj < 0i32.into())
    }

    fn as_f64_safe(&self) -> Option<f64> {
        let soorat = i32::try_from(&self.soorat).ok()?;
        let makhraj = i32::try_from(&self.makhraj).ok()?;
        const SAFE_LIMIT: i32 = 1_000_000;
        if soorat > SAFE_LIMIT || makhraj > SAFE_LIMIT {
            return None;
        }
        Some(soorat as f64 / makhraj as f64)
    }
}

impl Default for BigFraction {
    fn default() -> Self {
        Self {
            soorat: 0.into(),
            makhraj: 1.into(),
        }
    }
}

impl PartialEq for BigFraction {
    fn eq(&self, other: &Self) -> bool {
        &self.soorat * &other.makhraj == &self.makhraj * &other.soorat
    }
}

impl From<i32> for BigFraction {
    fn from(k: i32) -> Self {
        Self {
            soorat: k.into(),
            makhraj: 1.into(),
        }
    }
}

impl TryFrom<BigFraction> for i32 {
    type Error = ();

    fn try_from(_: BigFraction) -> std::result::Result<Self, Self::Error> {
        todo!()
    }
}

impl PartialOrd for BigFraction {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.is_negative(), other.is_negative()) {
            (true, false) => Some(Ordering::Greater),
            (false, true) => Some(Ordering::Less),
            _ => (&self.soorat * &other.makhraj).partial_cmp(&(&other.soorat * &self.makhraj)),
        }
    }
}

impl std::ops::Neg for BigFraction {
    type Output = BigFraction;

    fn neg(mut self) -> Self::Output {
        self.soorat *= -1;
        self
    }
}

impl std::ops::Add for BigFraction {
    type Output = BigFraction;

    fn add(mut self, rhs: Self) -> Self::Output {
        self.soorat = self.soorat * &rhs.makhraj + &self.makhraj * rhs.soorat;
        self.makhraj *= rhs.makhraj;
        self
    }
}

impl std::ops::Mul for BigFraction {
    type Output = BigFraction;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self.soorat *= rhs.soorat;
        self.makhraj *= rhs.makhraj;
        self
    }
}

impl ConstRepr for BigFraction {
    fn from_term(term: &Term) -> Option<Self> {
        match term {
            Term::NumberR { value, point } => Some(BigFraction {
                soorat: value.clone(),
                makhraj: BigInt::pow(&10.into(), *point as u32),
            }),
            _ => None,
        }
    }

    fn into_term(self) -> TermRef {
        todo!()
    }
}

#[derive(Clone, Copy, Debug)]
enum CmpOp {
    Lt,
    Le,
}

#[derive(Clone, Debug)]
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

fn convert(term: TermRef, arena: LogicArena<'_, RealIneq>) -> LogicValue<'_, RealIneq> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if detect_r_ty(ty) {
                        if unique_name == "eq" {
                            let d1 = Poly::<BigFraction>::from_subtract(op2.clone(), op1.clone());
                            if d1.is_zero() {
                                return LogicValue::True;
                            }
                            if d1.variables().is_empty() {
                                return LogicValue::False;
                            }
                            let mut d2 = d1.clone();
                            d2.negate();
                            let l1 = LogicValue::from(RealIneq(d1, CmpOp::Le));
                            let l2 = LogicValue::from(RealIneq(d2, CmpOp::Le));
                            return l1.and(l2, arena);
                        }
                        if unique_name == "lt" {
                            let d = Poly::<BigFraction>::from_subtract(op2.clone(), op1.clone());
                            if d.variables().is_empty() {
                                return if *d.constant() > 0i32.into() {
                                    LogicValue::True
                                } else {
                                    LogicValue::False
                                };
                            }
                            return LogicValue::from(RealIneq(d, CmpOp::Lt));
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
        success("0.5 * 0.5 = 0.25");
        fail("1. + 2. = 4.");
    }

    #[test]
    fn ring() {
        success("∀ x: ℝ, 0.5 * x + 0.5 * x = x");
    }

    #[test]
    fn lra_simple() {
        success("∀ x: ℝ, 0.5 * x > 3. -> x > 1.2 -> 0.6 * x > 3.");
        fail("∀ x: ℝ, 0.5 * x > 3. -> x > 1.2 -> 0.4 * x > 3.");
        success("∀ x: ℝ, x = 3. -> x < 3.01");
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
