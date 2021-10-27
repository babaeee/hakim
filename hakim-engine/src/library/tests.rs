use crate::engine::Engine;

#[test]
fn arith() {
    let mut eng = Engine::default();
    eng.load_library("Arith").unwrap();
}

#[test]
fn logic() {
    let mut eng = Engine::default();
    eng.load_library("Logic").unwrap();
}
