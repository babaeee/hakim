use crate::{
    app_ref,
    brain::{
        contains_wild, fill_wild, for_each_wild, get_forall_depth,
        infer::{type_of_and_infer, InferResults},
        map_reduce_wild, normalize, predict_axiom, subtype_and_infer, Term, TermRef,
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
            let t = map_reduce_wild(ty, &mut |x, _| Some(x), &std::cmp::min);
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
        let exp = self.infer.fill(self.exp.clone());
        let ty = self.infer.fill(self.ty.clone());
        let mut r = format!(
            "$in_applying \u{2068}{:?}\u{2069}\n$with_type \u{2068}{:?}\u{2069}\n$we_know:\n",
            exp, ty
        );
        let mut dep_list = vec![false; self.infer.n];
        let mut explore = |e| {
            for_each_wild(e, |t, _| {
                if t < dep_list.len() {
                    dep_list[t] = true;
                }
            });
        };
        for i in 0..self.infer.n {
            explore(&self.infer.tys[i]);
        }
        for i in dep_list
            .iter()
            .enumerate()
            .filter_map(|(i, x)| x.then(|| i))
        {
            if (Term::Wild { index: i, scope: 0 }) == *self.infer.terms[i].as_ref() {
                r += &format!("\u{2068}?w{} : {:?}\u{2069}\n", i, self.infer.tys[i]);
            }
        }
        r += "$and_we_should_proof:\n";
        for i in dep_list
            .iter()
            .enumerate()
            .filter_map(|(i, x)| (!x).then(|| i))
        {
            if (Term::Wild { index: i, scope: 0 }) == *self.infer.terms[i].as_ref() {
                r += &format!("\u{2068}{:?}\u{2069}\n", self.infer.tys[i]);
            }
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

fn find_args_in_apply_hyp(
    mut func: TermRef,
    op: TermRef,
    base_ic: usize,
    name: &str,
) -> Option<TermRef> {
    let fd = {
        let ty = type_of_and_infer(func.clone(), &mut InferResults::new(base_ic)).ok()?;
        get_forall_depth(&ty)
    };
    for ic in base_ic..base_ic + fd {
        let mut infers = InferResults::new(ic);
        let ty = match type_of_and_infer(app_ref!(func, op), &mut infers) {
            Ok(x) => x,
            Err(_) => {
                func = app_ref!(func, term_ref!(_ ic));
                continue;
            }
        };
        let mut flag = false;
        for i in 0..ic {
            if !contains_wild(&infers.terms[i]) {
                continue;
            }
            flag = true;
        }
        let ty = infers.fill(ty);
        if flag || predict_axiom(&ty, |x| x == name) {
            func = app_ref!(func, term_ref!(_ ic));
            continue;
        }
        return Some(ty);
    }
    None
}

fn apply_for_hyp(mut frame: Frame, exp: &str, name: &str) -> Result<Vec<Frame>> {
    let (term, ic) = frame.engine.parse_text_with_wild(exp)?;
    let prev_hyp = frame.remove_hyp_with_name(name)?.ty;
    let op = term_ref!(axiom name, prev_hyp);
    let ty = match find_args_in_apply_hyp(term, op, ic, name) {
        Some(x) => x,
        None => return Err(CanNotSolve("apply")),
    };
    frame.add_hyp_with_name(name, ty)?;
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
    subtype_and_infer(twa_ty.clone(), goal, &mut infers)?;
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

pub(crate) fn apply<'a>(
    frame: Frame,
    mut args: impl Iterator<Item = &'a str>,
) -> Result<Vec<Frame>> {
    let exp = &next_arg(&mut args, "apply")?;
    if let Some(in_kw) = args.next() {
        if in_kw != "in" {
            return Err(BadArg {
                tactic_name: "apply".to_string(),
                arg: in_kw.to_string(),
            });
        }
        if let Some(hyp) = args.next() {
            apply_for_hyp(frame, exp, hyp)
        } else {
            Err(BadArg {
                tactic_name: "apply".to_string(),
                arg: in_kw.to_string(),
            })
        }
    } else {
        apply_for_goal(frame, exp)
    }
}

#[cfg(test)]
mod tests {
    use crate::interactive::{
        tactic::Error,
        tests::{run_interactive, run_interactive_to_end, run_interactive_to_fail, EngineLevel},
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
    fn infer_sigma_factor_fn() {
        run_interactive(
            "∀ n: ℤ, 2 * sigma 0 (n + 1) (λ i: ℤ, i + 3) = sigma 0 (n + 1) (λ i: ℤ, 2 * (i+3))",
            r#"
            intros n
            apply sigma_factor
            "#,
            EngineLevel::Full,
        );
        run_interactive(
            "∀ n: ℤ, 2 * sigma 0 (n + 1) (λ i: ℤ, i) = sigma 0 (n + 1) (λ i: ℤ, 2 * i)",
            r#"
            intros n
            apply sigma_factor
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
    fn apply_on_depended_hyp() {
        run_interactive_to_fail("∀ f: ℤ -> U, ∀ n: ℤ, f n", "intros f n", "apply f in n");
    }

    // A regression test for out of bound array access in the FindInstance::question_text
    #[test]
    fn empty_intro_on_false() {
        let fail_tactic = "apply empty_intro";
        let mut session = run_interactive(
            "∀ A: U, ∀ a: A, a ∈ {} → False",
            "intros A a H",
            EngineLevel::Full,
        );
        match session.run_tactic(fail_tactic) {
            Ok(_) => panic!("tactic succeed but we need CanNotFindInstance failure"),
            Err(Error::CanNotFindInstance(e)) => {
                e.question_text();
            }
            Err(e) => panic!("We need CanNotFindInstance but found {:?}", e),
        }
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
