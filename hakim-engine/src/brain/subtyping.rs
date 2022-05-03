use super::{
    infer::{match_and_infer, InferResults},
    Result, TermRef,
};

//use super::{contains_wild, remove_unused_var, Abstraction, Term};

/// This function currently works equal to match and infer, but it is useful as a comment
/// to say we just need sub to be a subtype of super, not exactly equal to it, and we may
/// want to restore subtyping one day
pub fn subtype_and_infer(sub: TermRef, spr: TermRef, infers: &mut InferResults) -> Result<()> {
    match_and_infer(sub, spr, infers)
}

/*

#[derive(Debug, Clone, PartialEq, Eq)]
enum SubTypeAware {
    False,
    Imply(TermRef, TermRef),
    Or(TermRef, TermRef),
    Unknown(TermRef),
}

impl SubTypeAware {
    fn detect(term: TermRef) -> Self {
        match term.as_ref() {
            Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                "False" => SubTypeAware::False,
                _ => SubTypeAware::Unknown(term),
            },
            Term::Wild { .. }
            | Term::Universe { .. }
            | Term::Fun(_)
            | Term::Var { .. }
            | Term::Number { .. } => SubTypeAware::Unknown(term),
            Term::App { func, op: op2 } => match func.as_ref() {
                Term::App { func, op } => match func.as_ref() {
                    Term::Axiom { unique_name, .. } => match unique_name.as_str() {
                        "or" => SubTypeAware::Or(op2.clone(), op.clone()),
                        _ => SubTypeAware::Unknown(term),
                    },
                    _ => SubTypeAware::Unknown(term),
                },
                _ => SubTypeAware::Unknown(term),
            },
            Term::Forall(Abstraction { body, var_ty, .. }) => {
                if let Some(x) = remove_unused_var(body.clone(), 0) {
                    SubTypeAware::Imply(var_ty.clone(), x)
                } else {
                    SubTypeAware::Unknown(term)
                }
            }
        }
    }
}

pub fn subtype_and_infer(sub: TermRef, spr: TermRef, infers: &mut InferResults) -> Result<()> {
    if contains_wild(&sub) || contains_wild(&spr) {
        // FIXME: we currently give up on subtype inference with wilds
        return match_and_infer(sub, spr, infers);
    }
    let subc = SubTypeAware::detect(sub.clone());
    let sprc = SubTypeAware::detect(spr.clone());
    if subc == SubTypeAware::False {
        return Ok(());
    }
    if let (SubTypeAware::Imply(subl, subr), SubTypeAware::Imply(sprl, sprr)) =
        (subc.clone(), sprc.clone())
    {
        // function input is contra-variant, sub and super are reserverd
        subtype_and_infer(sprl, subl, infers)?;
        // function output is co-variant (normal)
        subtype_and_infer(subr, sprr, infers)?;
        return Ok(());
    }
    if let SubTypeAware::Or(a, b) = subc {
        subtype_and_infer(a, spr.clone(), infers)?;
        return subtype_and_infer(b, spr, infers);
    }
    if let SubTypeAware::Or(a, b) = sprc {
        let mut my_infers = infers.clone();
        if subtype_and_infer(sub.clone(), a, &mut my_infers).is_ok() {
            *infers = my_infers;
            return Ok(());
        }
        // previous infers is now polluted
        my_infers = infers.clone();
        if subtype_and_infer(sub.clone(), b, &mut my_infers).is_ok() {
            *infers = my_infers;
            return Ok(());
        }
    }
    match_and_infer(sub, spr, infers)
}

#[cfg(test)]
mod tests {
    use crate::engine::Engine;

    fn is_subtype(sub: &str, spr: &str) -> bool {
        let query = format!("∀ A B C D E F: Universe, ∀ a: ({sub}), (λ x: ({spr}), False) a");
        let eng = Engine::default();
        let r = eng.parse_text(&query);
        r.is_ok()
    }

    #[test]
    fn false_simple() {
        //assert!(is_subtype("False", "2 = 3"));
        //assert!(is_subtype("False", "2 = 2"));
        assert!(is_subtype("False", "A"));
        assert!(is_subtype("False", "A ∨ B"));
        assert!(!is_subtype("A", "False"));
        assert!(!is_subtype("A ∨ False", "False"));
    }

    #[test]
    fn or() {
        assert!(is_subtype("A", "A ∨ B"));
        assert!(is_subtype("A", "A ∨ B ∨ C"));
        assert!(is_subtype("A ∨ B", "A ∨ B ∨ C"));
        assert!(is_subtype("A ∨ C", "A ∨ B ∨ C"));
        assert!(is_subtype("A", "A ∨ A"));
        assert!(is_subtype("A ∨ A", "A"));
        assert!(is_subtype("A ∨ False", "A"));
        assert!(!is_subtype("A ∨ B", "A"));
        assert!(!is_subtype("A ∨ B", "A"));
    }

    #[test]
    fn imply() {
        assert!(is_subtype("A ∨ B -> C", "A -> C"));
        assert!(is_subtype("~ (A ∨ B)", "A -> C"));
        assert!(!is_subtype("~ (A ∨ B)", "A"));
        assert!(is_subtype("~ A", "A -> B"));
        assert!(!is_subtype("A -> B", "~ A"));
        assert!(!is_subtype("A -> B", "B"));
    }
}

*/
