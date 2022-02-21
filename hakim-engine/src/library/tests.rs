use crate::engine::Engine;

const LIB_NAMES: [&str; 8] = ["All", "Arith", "Logic", "Eq", "NumberTheory", "Sigma", "Set", "Induction"];

#[test]
fn all() {
    let mut eng = Engine::default();
    for lib in LIB_NAMES {
        eng.load_library(lib).unwrap();
    }
}

#[test]
fn any() {
    for lib in LIB_NAMES {
        Engine::default().load_library(lib).unwrap();
    }
}
