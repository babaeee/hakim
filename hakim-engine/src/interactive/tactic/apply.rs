use crate::{
    app_ref,
    brain::{
        contains_wild, fill_wild, for_each_wild, get_forall_depth,
        infer::{type_of_and_infer, InferResults, VarCategory},
        map_reduce_wild, normalize, predict_axiom, subtype_and_infer, Term, TermRef,
    },
    engine::Engine,
    interactive::Frame,
    term_ref,
};

use super::{next_arg, Error::*, Result};

#[derive(Debug, Clone)]
pub struct FindInstance {
    infer: InferResults,
    exp: TermRef,
    ty: TermRef,
    engine: Engine,
}

impl FindInstance {
    pub(crate) fn first_needed_wild(&self) -> usize {
        if let Some(x) = self.infer.unresolved_obligations.get(0) {
            return x.var;
        }
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
            for_each_wild(e, |t, _| match VarCategory::from(t) {
                VarCategory::Term(i) => dep_list[i] = true,
                VarCategory::Ty(_) => (),
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
            if self.infer.terms[i] == VarCategory::Term(i).to_term(0) {
                r += &format!("\u{2068}?{} : {:?}\u{2069}\n", i, self.infer.tys[i]);
            }
        }
        r += "$and_we_should_proof:\n";
        for i in dep_list
            .iter()
            .enumerate()
            .filter_map(|(i, x)| (!x).then(|| i))
        {
            if self.infer.terms[i] == VarCategory::Term(i).to_term(0) {
                r += &format!("\u{2068}{:?}\u{2069}\n", self.infer.tys[i]);
            }
        }
        r += &format!(
            "\n$enter_value_of1 \u{2068}?{}\u{2069} $enter_value_of2:\n",
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
) -> Option<(TermRef, InferResults)> {
    let mut global_infers = InferResults::new(base_ic);
    let fd = {
        let ty = type_of_and_infer(func.clone(), &mut global_infers).ok()?;
        get_forall_depth(&ty)
    };
    for _ in base_ic..base_ic + fd {
        let mut infers = global_infers.clone();
        let ty = match type_of_and_infer(app_ref!(func, op), &mut infers) {
            Ok(x) => x,
            Err(_) => {
                func = app_ref!(func, global_infers.add_var());
                continue;
            }
        };
        let ty = infers.fill(ty);
        if predict_axiom(&ty, |x| x == name) {
            func = app_ref!(func, global_infers.add_var());
            continue;
        }
        return Some((ty, infers));
    }
    None
}

fn apply_for_hyp(mut frame: Frame, exp: &str, name: &str) -> Result<Vec<Frame>> {
    let orig_frame = frame.clone();
    let (term, ic) = frame.engine.parse_text_with_wild(exp)?;
    let prev_hyp = frame.remove_hyp_with_name(name)?.ty;
    let op = term_ref!(axiom name, prev_hyp);
    let (ty, infers) = match find_args_in_apply_hyp(term, op, ic, name) {
        Some(x) => x,
        None => return Err(CanNotSolve("apply")),
    };
    frame.add_hyp_with_name(name, ty)?;
    let mut fs = vec![frame];
    for i in 0..infers.n {
        let mut frame = orig_frame.clone();
        if !contains_wild(&infers.terms[i]) {
            continue;
        }
        if !contains_wild(&infers.tys[i]) {
            frame.goal = normalize(infers.tys[i].clone());
            fs.push(frame);
        } else {
            return Err(CanNotSolve("apply_hyp"));
        }
    }
    Ok(fs)
}

fn apply_for_goal(frame: Frame, exp: &str) -> Result<Vec<Frame>> {
    let (term, inf_num) = frame.engine.parse_text_with_wild(exp)?;
    let ty = type_of_and_infer(term.clone(), &mut InferResults::new(inf_num))?;
    let goal = frame.goal.clone();
    let d_forall = get_forall_depth(&ty);
    for i in 0..=d_forall {
        if let Ok(x) =
            try_argument_count_for_goal(term.clone(), i, inf_num, goal.clone(), frame.clone())
        {
            return Ok(x);
        }
    }
    let d_forall = d_forall
        .checked_sub(get_forall_depth(&goal))
        .ok_or(CanNotSolve("apply"))?;
    try_argument_count_for_goal(term, d_forall, inf_num, goal, frame)
}

fn try_argument_count_for_goal(
    mut term: std::rc::Rc<Term>,
    d_forall: usize,
    inf_num: usize,
    goal: std::rc::Rc<Term>,
    frame: Frame,
) -> Result<Vec<Frame>> {
    let mut infers = InferResults::new(inf_num);
    for _ in 0..d_forall {
        term = app_ref!(term, infers.add_var());
    }
    let twa_ty = type_of_and_infer(term.clone(), &mut infers)?;
    subtype_and_infer(twa_ty.clone(), goal, &mut infers)?;
    if !infers.unresolved_obligations.is_empty() {
        return Err(CanNotFindInstance(Box::new(FindInstance {
            engine: frame.engine,
            infer: infers,
            exp: term,
            ty: twa_ty,
        })));
    }
    let mut v = vec![];
    for i in 0..infers.n {
        let mut frame = frame.clone();
        if !contains_wild(&infers.terms[i]) {
            continue;
        }
        if !contains_wild(&infers.tys[i]) {
            frame.goal = normalize(infers.tys[i].clone());
            v.push(frame);
        } else {
            return Err(CanNotFindInstance(Box::new(FindInstance {
                engine: frame.engine,
                infer: infers,
                exp: term,
                ty: twa_ty,
            })));
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
    fn apply_hyp_multi_inp() {
        run_interactive_to_end(
            "∀ x, 2 * x = 2 * 4 -> x = 4",
            r#"
            intros x H
            apply eq_mult_l in H
            lia
            apply H
        "#,
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

    #[test]
    fn infer_induction_p() {
        run_interactive(
            "∀ a n: ℤ, 0 ≤ n → 0 < a → 0 < a ^ n",
            r#"
            intros a
            apply z_simple_induction"#,
            EngineLevel::Full,
        );
    }

    #[test]
    fn soundness_bug_simple_recursion() {
        run_interactive_to_fail(
            "∃ f: ℤ → ℤ, f 0 = 1 ∧ ∀ n: ℤ, 0 ≤ n → f (n + 1) = n * f (n + 2)",
            r#""#,
            "apply z_simple_recursion",
        );
    }

    fn instance_recovery(
        goal: &str,
        tactics: &str,
        fail_tactic: &str,
        first_wild: usize,
        answer: &str,
    ) {
        let mut se = run_interactive(goal, tactics, EngineLevel::Full);
        let e = se.run_tactic(fail_tactic);
        if let Err(Error::CanNotFindInstance(e)) = e {
            assert_eq!(e.first_needed_wild(), first_wild);
            let tac = e.tactic_by_answer(answer).unwrap();
            se.run_tactic(&tac).unwrap();
            return;
        }
        panic!("Expected to not finding instance");
    }

    #[test]
    fn recover_instance_lt_trans() {
        instance_recovery(
            "forall a b c d: ℤ, a < b -> c < d -> a + c < b + d",
            r#"
        intros a b c d a_lt_b c_lt_d
        add_hyp (a + c < b + c)
        apply lt_plus_r
        apply a_lt_b
        add_hyp (b + c < b + d)
        apply lt_plus_l
        apply c_lt_d"#,
            "apply lt_trans",
            2,
            "b + c",
        );
    }

    #[test]
    fn recover_instance_z_recursion() {
        instance_recovery(
            "∃ f: ℤ → ℤ, f 0 = 1 ∧ ∀ n: ℤ, 0 ≤ n → f (n + 1) = n * f n",
            r#""#,
            "apply z_simple_recursion",
            6,
            "λ n pf, n * pf",
        );
    }
}
