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

fn convert_calculator_mode(
    term: TermRef,
    arena: LogicArena<'_, Poly<BigFraction>>,
) -> LogicValue<'_, Poly<BigFraction>> {
    let r = convert(term, arena);
    fn is_good(x: &LogicValue<'_, Poly<BigFraction>>) -> bool {
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

fn convert(
    term: TermRef,
    arena: LogicArena<'_, Poly<BigFraction>>,
) -> LogicValue<'_, Poly<BigFraction>> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "eq" && detect_r_ty(ty) {
                        let mut d1 = Poly::<BigFraction>::from_subtract(op2.clone(), op1.clone());
                        if d1.is_zero() {
                            return LogicValue::True;
                        }
                        if d1.variables().is_empty() {
                            return LogicValue::False;
                        }
                        d1.add(1.into());
                        let mut d2 = Poly::<BigFraction>::from_subtract(op1.clone(), op2.clone());
                        d2.add(1.into());
                        let l1 = LogicValue::from(d1);
                        let l2 = LogicValue::from(d2);
                        return l1.and(l2, arena);
                    }
                }
            }
        }
    }
    LogicValue::unknown()
}

fn check_contradiction_lp(_: usize, _: &[LinearPoly<BigFraction>]) -> bool {
    false
}

fn check_contradiction(polies: &[Poly<BigFraction>]) -> bool {
    let (var_cnt, linear_polies) = LinearPoly::from_slice(polies);
    check_contradiction_lp(var_cnt, &linear_polies)
}

fn negator(mut poly: Poly<BigFraction>) -> Poly<BigFraction> {
    poly.negate();
    poly.add(1.into());
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
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

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
        fail("1. + 2. = 4.");
    }

    #[test]
    fn ring() {
        success("∀ x: ℝ, 0.5 * x + 0.5 * x = x");
    }
}
