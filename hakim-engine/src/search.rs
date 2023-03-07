use crate::{
    brain::{
        infer::{match_and_infer, InferResults, VarCategory},
        subst, TermRef,
    },
    engine::{Engine, Result},
    parser::is_valid_ident,
    Abstraction, Term,
};

fn search_with_name(engine: &Engine, name: &str) -> Vec<String> {
    engine
        .lib_iter()
        .map(|(a, _)| a)
        .filter(|x| x.contains(name))
        .map(|x| x.to_string())
        .collect()
}

pub fn search(engine: &Engine, query: &str) -> Result<Vec<String>> {
    if is_valid_ident(query) {
        return Ok(search_with_name(engine, query));
    }
    let (qt, infer_cnt) = engine.parse_text_with_wild(query)?;
    Ok(engine
        .lib_iter()
        .filter_map(|(name, mut ty)| {
            let mut infers = InferResults::new(infer_cnt);
            if is_match(qt.clone(), ty.clone(), infers.clone(), infer_cnt) {
                return Some(name.to_string());
            }
            while let Term::Forall(Abstraction { body, .. }) = ty.as_ref() {
                ty = subst(body.clone(), infers.add_var_top_level());
                if is_match(qt.clone(), ty.clone(), infers.clone(), infer_cnt) {
                    return Some(name.to_string());
                }
            }
            None
        })
        .collect())
}

fn is_match(qt: TermRef, ty: TermRef, mut infers: InferResults, infer_cnt: usize) -> bool {
    if match_and_infer(qt, ty, &mut infers).is_err() {
        return false;
    }
    let mut good = vec![false; infer_cnt];
    for i in infer_cnt..infers.n {
        let t = infers.get(i);
        if let Term::Wild { index, .. } = t.as_ref() {
            let index = *index / 2;
            if index < infer_cnt {
                good[index] = true;
            }
        }
    }
    for (i, is_good) in good.into_iter().enumerate() {
        if is_good {
            continue;
        }
        if let Term::Wild { index, .. } = &infers.terms[i].as_ref() {
            if VarCategory::from(*index) == VarCategory::Term(i) {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use std::panic::catch_unwind;

    use crate::engine::Engine;

    const DEFAULT_LIBS: &str = r#"/Arith
    /Logic
    /Eq"#;

    fn build_engine(libs: &str) -> Engine {
        let mut eng = Engine::default();
        for lib in libs.lines() {
            eng.load_library(lib).unwrap();
        }
        eng
    }

    fn do_search(query: &str) {
        let eng = build_engine(DEFAULT_LIBS);
        let r = eng.search(query).unwrap();
        for x in r {
            let r = catch_unwind(|| {
                let ty = eng.calc_type_and_infer(&x).unwrap();
                format!("{}: {:?}\n", x, ty);
            });
            r.unwrap_or_else(|_| panic!("broken search item showing in {x}"));
        }
    }

    fn check_search(query: &str, list: &str, libs: &str) {
        let eng = build_engine(libs);
        let mut result = eng.search(query).unwrap();
        let mut items = list
            .lines()
            .map(|x| x.trim())
            .filter(|x| !x.is_empty())
            .collect::<Vec<_>>();
        items.sort_unstable();
        result.sort_unstable();
        assert_eq!(items, result);
    }

    #[test]
    fn lt_z() {
        check_search(
            "∀ a b c: ℤ, ?x < ?y -> ?a + ?b < ?c + ?d",
            r#"
            lt_plus_r
            lt_plus_l
        "#,
            DEFAULT_LIBS,
        );
    }

    #[test]
    fn lt_plus() {
        check_search(
            "? + ? < ? + ?",
            r#"
            lt_plus_r
            lt_plus_l
        "#,
            DEFAULT_LIBS,
        );
    }

    #[test]
    fn forall_depth() {
        check_search(
            "forall A B:?, is_cut A -> ?",
            r#"
        P_hold_for_multi
        P_hold_for_multi_not_complete
        cut_minus
        cut_mult_pos
        cut_mult_pos_is_cut
        cut_plus
        cut_plus_is_cut
        ex_proof
        set_from_func_unfold
        set_induction
        z_induction_simple
        z_induction_strong
        "#,
            "/RArith",
        );
    }

    #[test]
    fn empty_search_dont_panic() {
        do_search("?");
    }

    #[test]
    fn dont_stack_overflow() {
        check_search(
            "?x -> ?x -> ?x -> ?x",
            r"
        P_hold_for_multi
        P_hold_for_multi_not_complete
        contpos
        ex_proof
        if_f
        iff_imp_l
        iff_imp_r
        imply_trans
        list_induction_len
        set_from_func_unfold
        set_induction
        z_induction_simple
        z_induction_strong
        ",
            DEFAULT_LIBS,
        );
    }

    #[test]
    fn dont_stack_overflow2() {
        do_search("∃ x, ? < x / 1 * ?");
    }

    #[test]
    fn panic_in_infer() {
        do_search("∃ x, ?");
    }
}
