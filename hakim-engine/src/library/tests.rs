use crate::engine::Engine;

#[test]
fn arith() {
    let mut eng = Engine::default();
    eng.load_library("Arith").unwrap();
}
