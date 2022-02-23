use super::{Error::*, Result};
use crate::{
    analysis::{
        arith::Poly,
        logic::{LogicArena, LogicBuilder, LogicTree},
    },
    brain::{Term, TermRef},
    interactive::Frame,
};

fn convert(term: TermRef, arena: LogicArena<'_, Poly>) -> &LogicTree<'_, Poly> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "lt" {
                    let d = Poly::from_subtract(op2.clone(), op1.clone());
                    return arena.alloc(LogicTree::Atom(d));
                }
            }
        }
    }
    arena.alloc(LogicTree::Unknown)
}

fn check_contradiction(polies: &[Poly]) -> bool {
    polies
        .iter()
        .any(|x| x.variables().is_empty() && *x.constant() <= 0.into())
}

fn negator(mut poly: Poly) -> Poly {
    poly.negate();
    poly.add(1.into());
    poly
}

pub fn lia(frame: Frame) -> Result<Vec<Frame>> {
    let logic_builder = LogicBuilder::new(convert);
    logic_builder.and_not_term(frame.goal);
    for (_, hyp) in frame.hyps {
        logic_builder.and_term(hyp);
    }
    if logic_builder.check_contradiction(check_contradiction, negator) {
        Ok(vec![])
    } else {
        Err(CanNotSolve("lia"))
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::run_interactive_to_end;

    #[test]
    fn success_lia_goal() {
        run_interactive_to_end("forall x: ℤ, x < x + 1", "intros\nlia");
    }

    #[test]
    fn success_lia_hyp() {
        run_interactive_to_end("forall x: ℤ, x + 2 < x + 1 -> False", "intros\nlia");
    }
}
