use super::{Error::*, Result};
use crate::{
    analysis::arith::Poly,
    brain::{Term, TermRef},
    interactive::Frame,
};

// remove me!
pub fn get_lt_params(term: &TermRef) -> Option<[TermRef; 2]> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "lt" {
                    return Some([op1.clone(), op2.clone()]);
                }
            }
        }
    }
    None
}

pub fn lia(frame: Frame) -> Result<Vec<Frame>> {
    let goal = frame.goal;
    let [op1, op2] = get_lt_params(&goal).ok_or(BadGoal("not implemented"))?;
    let d = Poly::from_subtract(op2, op1);
    if *d.constant() > 0.into() && d.variables().is_empty() {
        Ok(vec![])
    } else {
        Err(CanNotSolve("lia"))
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn success_lia1() {
        run_interactive_to_end(
            "forall x: ℤ, x < x + 1",
            r#"
        intros x
        lia
        "#,
        );
    }
}
