use crate::{brain::TermRef, engine::Engine};

#[test]
fn all() {
    let mut eng = Engine::default();
    eng.load_library("Arith").unwrap();
    eng.load_library("Logic").unwrap();
    eng.load_library("Eq").unwrap();
    eng.load_library("Sigma").unwrap();
}
