use crate::{
    brain::{
        get_forall_depth,
        infer::{match_and_infer, InferResults},
        subst,
    },
    engine::{Engine, Result},
    parser::is_valid_ident,
    term_ref, Abstraction, Term,
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
    let forall_cnt = get_forall_depth(&qt);
    Ok(engine
        .lib_iter()
        .filter_map(|(name, ty)| {
            let mut our_infer_cnt = infer_cnt;
            let their_forall_cnt = get_forall_depth(&ty);
            if forall_cnt > their_forall_cnt {
                return None;
            }
            let forall_diff = their_forall_cnt - forall_cnt;
            let mut ty_subst = ty;
            for _ in 0..forall_diff {
                if let Term::Forall(Abstraction { body, .. }) = ty_subst.as_ref() {
                    let w = term_ref!(_ our_infer_cnt);
                    our_infer_cnt += 1;
                    ty_subst = subst(body.clone(), w);
                } else {
                    return None;
                }
            }
            let mut infers = InferResults::new(our_infer_cnt);
            match_and_infer(qt.clone(), ty_subst, &mut infers).ok()?;
            let mut good = vec![false; infer_cnt];
            for i in infer_cnt..our_infer_cnt {
                let t = infers.get(i);
                if let Term::Wild { index, .. } = t.as_ref() {
                    if *index < infer_cnt {
                        good[*index] = true;
                    }
                }
            }
            for (i, is_good) in good.into_iter().enumerate() {
                if is_good {
                    continue;
                }
                if let Term::Wild { index, .. } = infers.get(i).as_ref() {
                    if *index == i {
                        return None;
                    }
                }
            }
            Some(name.to_string())
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use std::panic::catch_unwind;

    use crate::engine::Engine;

    fn build_engine() -> Engine {
        let mut eng = Engine::default();
        eng.load_library("Arith").unwrap();
        eng.load_library("Logic").unwrap();
        eng.load_library("Eq").unwrap();
        eng
    }

    fn do_search(query: &str) {
        let eng = build_engine();
        let r = eng.search(query).unwrap();
        for x in r {
            let r = catch_unwind(|| {
                let ty = eng.calc_type(&x).unwrap();
                format!("{}: {:?}\n", x, ty);
            });
            r.unwrap_or_else(|_| panic!("broken search item showing in {x}"));
        }
    }

    fn check_search(query: &str, list: &str) {
        let eng = build_engine();
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
        );
    }

    #[test]
    fn empty_search_dont_panic() {
        do_search("?");
    }

    #[test]
    fn dont_stack_overflow() {
        check_search("?x -> ?x -> ?x -> ?x", "");
    }
}
