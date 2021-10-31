use crate::{
    brain::infer::{match_and_infer, InferResults},
    engine::{Engine, Result},
};

pub fn search(engine: &Engine, query: &str) -> Result<Vec<String>> {
    let (qt, infer_cnt) = engine.parse_text_with_wild(query)?;
    Ok(engine
        .lib_iter()
        .filter_map(|(name, ty)| {
            let mut infers = InferResults::new(infer_cnt);
            match_and_infer(qt.clone(), ty, &mut infers).ok()?;
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
        items.sort();
        result.sort();
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
}
