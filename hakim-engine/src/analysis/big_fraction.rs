use std::cmp::Ordering;

use num_bigint::BigInt;

use crate::{
    app_ref,
    brain::{Term, TermRef},
    library::prelude::{div, z},
    term_ref,
};

use super::arith::ConstRepr;

#[derive(Debug, Clone)]
pub struct BigFraction {
    soorat: BigInt,
    /// always bigger than zero
    makhraj: BigInt,
}

impl BigFraction {
    pub fn as_f64_safe(&self) -> Option<f64> {
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

impl Eq for BigFraction {}

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
        (&self.soorat * &other.makhraj).partial_cmp(&(&other.soorat * &self.makhraj))
    }
}

impl Ord for BigFraction {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.soorat * &other.makhraj).cmp(&(&other.soorat * &self.makhraj))
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
            Term::Number { value } => Some(BigFraction {
                soorat: value.clone(),
                makhraj: 1.into(),
            }),
            Term::NumberR { value, point } => Some(BigFraction {
                soorat: value.clone(),
                makhraj: BigInt::pow(&10.into(), *point as u32),
            }),
            _ => None,
        }
    }

    fn into_term(self) -> TermRef {
        app_ref!(
            div(),
            z(),
            term_ref!(n self.soorat),
            term_ref!(n self.makhraj)
        )
    }

    fn mult_inverse(mut self) -> Self {
        if self.soorat == 0.into() {
            return BigFraction::default();
        }
        if self.soorat < 0.into() {
            self.soorat *= -1;
            self.makhraj *= -1;
        }
        BigFraction {
            soorat: self.makhraj,
            makhraj: self.soorat,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BigFraction;

    #[test]
    fn negative_is_less_than_zero() {
        assert!(BigFraction::from(-1) < BigFraction::from(0));
    }
}
