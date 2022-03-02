use crate::engine::Engine;

use super::{
    ast::{File, Sentence},
    text_of_name,
};

const LIB_NAMES: [&str; 9] = [
    "All",
    "Arith",
    "Logic",
    "Eq",
    "NumberTheory",
    "ProductOperator",
    "Sigma",
    "Set",
    "Induction",
];

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

#[test]
fn check_library_proofs() {
    for lib_name in LIB_NAMES {
        let mut eng = Engine::default();
        let lib = File::parse(text_of_name(lib_name).unwrap());
        for st in lib.0 {
            if let Sentence::Theorem { name, proof, ty } = &st {
                let mut session = eng.interactive_session(ty).unwrap();
                for tactic in proof {
                    match session.run_tactic(tactic) {
                        Ok(_) => (),
                        Err(e) => panic!(
                            "In library {}\nIn theorem {}: {}\nProof failed with error: {:?}",
                            lib_name, name, ty, e
                        ),
                    }
                }
            }
            st.add_to_engine(&mut eng).unwrap();
        }
    }
}
