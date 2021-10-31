use crate::{
    brain::{
        get_forall_depth,
        infer::{match_and_infer, InferResults},
        subst,
    },
    engine::{Engine, Result},
    term_ref, Abstraction, Term,
};

pub fn search(engine: &Engine, query: &str) -> Result<Vec<String>> {
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
            Some(name.to_string())
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use crate::engine::Engine;

    fn build_engine() -> Engine {
        let mut eng = Engine::default();
        eng.load_library("Arith").unwrap();
        eng.load_library("Logic").unwrap();
        eng.load_library("Eq").unwrap();
        eng
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
            "∀ a b c: ℤ, _0 < _1 -> _2 + _3 < _4 + _5",
            r#"
            lt_plus_r
            lt_plus_l
        "#,
        );
    }

    #[test]
    fn dont_stack_overflow() {
        check_search("_0 -> _0 -> _0 -> _0", "");
    }
}
