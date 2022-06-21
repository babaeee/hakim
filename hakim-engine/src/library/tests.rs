use std::panic::catch_unwind;

use crate::engine::Engine;

use super::{
    ast::{File, Sentence},
    text::all_names,
    text_of_name,
};

#[test]
fn all() {
    let mut eng = Engine::default();
    for lib in all_names() {
        eng.load_library(dbg!(lib)).unwrap();
    }
}

#[test]
fn any() {
    for lib in all_names() {
        let r = catch_unwind(|| {
            Engine::default().load_library(lib).unwrap();
        });
        dbg!(&lib);
        if let Err(e) = r {
            panic!("error in {lib}, {e:?}");
        }
    }
}

#[test]
fn check_library_proofs() {
    for lib_name in all_names() {
        let mut eng = Engine::default();
        let lib = File::parse(text_of_name(lib_name).unwrap());
        for st in lib.0 {
            if let Sentence::Theorem { name, proof, ty } = &st {
                let mut session = eng.interactive_session(ty).unwrap();
                for tactic in proof {
                    match session.run_tactic(tactic) {
                        Ok(_) => (),
                        Err(e) => panic!(
                            "In library {lib_name}\nIn theorem {name}: {ty}\nIn tactic: {tactic}\nProof failed with error: {e:?}",
                        ),
                    }
                }
                assert!(
                    session.is_finished(),
                    "Incomplete proof for {name} in library {lib_name}"
                );
            }
            st.add_to_engine(&mut eng).unwrap();
        }
    }
}
