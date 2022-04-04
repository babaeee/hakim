use super::{rewrite::get_eq_params, Error::*, Result};
use crate::{analysis::arith::Poly, interactive::Frame};

pub fn ring(frame: Frame) -> Result<Vec<Frame>> {
    let goal = frame.goal;
    let [op1, op2, _] = get_eq_params(&goal).ok_or(BadGoal("ring only work on equality"))?;
    let d = Poly::from_subtract(op1, op2);
    dbg!(&d);
    if d.is_zero() {
        Ok(vec![])
    } else {
        Err(CanNotSolve("ring"))
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nring");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "lia");
    }

    #[test]
    fn minus() {
        success("∀ x: ℤ, x - x = 0");
        fail("∀ x: ℤ, x - x = 1");
    }

    #[test]
    fn success_ring1() {
        success("∀ x: ℤ, x + x = 2 * x");
    }

    #[test]
    fn success_ring2() {
        success(
            "forall a b: ℤ, eq ℤ (mult (plus a b) (plus a b)) \
            (plus (mult a a) (plus (mult 2 (mult a b)) (mult b b)))",
        );
    }
}
