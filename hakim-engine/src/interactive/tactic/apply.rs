use crate::{
    app_ref,
    brain::{
        contains_wild, fill_wild, get_forall_depth,
        infer::{match_and_infer, type_of_and_infer, InferResults},
        map_reduce_wild, normalize, predict_axiom, Term, TermRef,
    },
    engine::Engine,
    interactive::Frame,
    term_ref,
};

use super::{next_arg, Error::*, Result};

#[derive(Debug)]
pub struct FindInstance {
    infer: InferResults,
    exp: TermRef,
    ty: TermRef,
    engine: Engine,
}

impl FindInstance {
    pub(crate) fn first_needed_wild(&self) -> usize {
        let mut r = None;
        for ty in &self.infer.tys {
            let t = map_reduce_wild(ty, &|x, _| Some(x), &std::cmp::min);
            if let Some(tv) = t {
                if let Some(rv) = r {
                    if rv > tv {
                        r = t;
                    }
                } else {
                    r = t;
                }
            }
        }
        r.unwrap()
    }

    pub fn question_text(&self) -> String {
        let mut r = format!(
            "$in_applying \u{2068}{:?}\u{2069}\n$with_type \u{2068}{:?}\u{2069}\n$we_know:\n",
            self.exp, self.ty
        );
        for i in 0..self.infer.n {
            r += &if let Term::Wild { index: i, scope: _ } = *self.infer.terms[i].as_ref() {
                format!("\u{2068}?w{} : {:?}\u{2069}\n", i, self.infer.tys[i])
            } else {
                format!(
                    "\u{2068}?w{} = {:?} : {:?}\u{2069}\n",
                    i, self.infer.terms[i], self.infer.tys[i]
                )
            };
        }
        r += &format!(
            "\n$enter_value_of1 \u{2068}?w{}\u{2069} $enter_value_of2:\n",
            self.first_needed_wild()
        );
        r
    }

    pub fn tactic_by_answer(self, filler: &str) -> Result<String> {
        let filler = self.engine.parse_text(filler)?;
        let id = self.first_needed_wild();
        let exp = fill_wild(self.exp, &|x, _| {
            if x == id {
                filler.clone()
            } else {
                term_ref!(_ x)
            }
        });
        Ok(format!("apply ({:?})", exp))
    }
}

fn apply_for_hyp(mut frame: Frame, exp: &str, name: String) -> Result<Vec<Frame>> {
    let (term, ic) = frame.engine.parse_text_with_wild(exp)?;
    let prev_hyp = frame.remove_hyp_with_name(name.clone())?;
    let mut infers = InferResults::new(ic);
    let ty = type_of_and_infer(app_ref!(term, term_ref!(axiom name, prev_hyp)), &mut infers)?;
    for i in 0..ic {
        if !contains_wild(&infers.terms[i]) {
            continue;
        }
        todo!();
    }
    let ty = infers.fill(ty);
    if predict_axiom(&ty, &|x| x == name) {
        return Err(ContextDependOnHyp(name, ty));
    }
    frame.add_hyp_with_name(&name, ty)?;
    Ok(vec![frame])
}

fn apply_for_goal(frame: Frame, exp: &str) -> Result<Vec<Frame>> {
    let (term, mut inf_num) = frame.engine.parse_text_with_wild(exp)?;
    let ty = type_of_and_infer(term.clone(), &mut InferResults::new(inf_num))?;
    let goal = frame.goal.clone();
    let d_forall = get_forall_depth(&ty)
        .checked_sub(get_forall_depth(&goal))
        .ok_or(CanNotSolve("apply"))?;
    let mut twa = term;
    for _ in 0..d_forall {
        twa = app_ref!(twa, term_ref!(_ inf_num));
        inf_num += 1;
    }
    let mut infers = InferResults::new(inf_num);
    let twa_ty = type_of_and_infer(twa.clone(), &mut infers)?;
    match_and_infer(twa_ty.clone(), goal, &mut infers)?;
    let mut v = vec![];
    for i in 0..inf_num {
        let mut frame = frame.clone();
        if !contains_wild(&infers.terms[i]) {
            continue;
        }
        if !contains_wild(&infers.tys[i]) {
            frame.goal = normalize(infers.tys[i].clone());
            v.push(frame);
        } else {
            return Err(CanNotFindInstance(FindInstance {
                engine: frame.engine,
                infer: infers,
                exp: twa,
                ty: twa_ty,
            }));
        }
    }
    Ok(v)
}

pub(crate) fn apply(frame: Frame, mut args: impl Iterator<Item = String>) -> Result<Vec<Frame>> {
    let exp = &next_arg(&mut args, "apply")?;
    if let Some(in_kw) = args.next() {
        if in_kw != "in" {
            return Err(BadArg {
                tactic_name: "apply".to_string(),
                arg: in_kw,
            });
        }
        if let Some(hyp) = args.next() {
            apply_for_hyp(frame, exp, hyp)
        } else {
            Err(BadArg {
                tactic_name: "apply".to_string(),
                arg: in_kw,
            })
        }
    } else {
        apply_for_goal(frame, exp)
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{
        run_interactive, run_interactive_to_end, run_interactive_to_fail, EngineLevel,
    };

    #[test]
    fn infer_tohi_type() {
        run_interactive(
            "{} ⊆ {2}",
            r#"
            apply included_fold
            intros a
            "#,
            EngineLevel::Full,
        );
    }

    #[test]
    fn exists_destruct() {
        run_interactive_to_end(
            "∀ P: ℤ -> U, (∀ x: ℤ, P x -> P (2*x)) -> (∃ b: ℤ, P b) -> ∃ b: ℤ, P (2*b)",
            r#"
            intros P px_p2x exP
            apply (ex_ind ? ? exP)
            intros exP_value exP_proof
            apply (ex_intro ? ? exP_value)
            apply px_p2x
            apply exP_proof
        "#,
        )
    }

    #[test]
    fn apply_on_forall_no_overflow() {
        run_interactive_to_fail(
            "∀ T: U, ∀ A B C: set T, A ⊆ B -> B ⊆ C -> A ⊆ C",
            "",
            "apply included_fold",
        );
    }

    #[test]
    fn forall_not_exist() {
        run_interactive_to_end(
            "∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False",
            r#"
            intros A P fa exi
            apply (ex_ind ? ? exi)
            intros exv exv_not_p
            apply (exv_not_p (fa exv))
        "#,
        );
        run_interactive_to_end(
            "∀ A: U, ∀ P: A -> U, (∀ x: A, P x) -> (∃ x: A, P x -> False) -> False",
            r#"
            intros A P fa exi
            apply (ex_ind ? ? exi)
            intros exv exv_not_p
            apply exv_not_p
            apply fa
        "#,
        );
    }
}
