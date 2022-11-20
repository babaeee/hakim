use std::panic::catch_unwind;

use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use crate::{engine::Engine, library::ast::Signature};

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
    let names = all_names().collect::<Vec<_>>();
    names.par_iter().for_each(|lib_name| {
        let mut eng = Engine::default();
        let lib = File::parse(text_of_name(lib_name).unwrap());
        eprintln!("lib {lib_name} started");
        for st in lib.0 {
            if let Sentence::Theorem { sig, proof } = &st {
                let Signature { ty, name, .. } = sig;
                let mut session = eng.interactive_session(ty).unwrap();
                for (i, tactic) in proof.iter().enumerate() {
                    match session.run_tactic(tactic) {
                        Ok(_) => (),
                        Err(e) => panic!(
                            "In library {lib_name}\nIn theorem {name}: {ty}\nIn tactic: {tactic} ({i})\nProof failed with error: {e:?}\nMonitor: {}",
                            session.monitor_string(),
                        ),
                    }
                }
                assert!(
                    session.is_finished(),
                    "Incomplete proof for {name} in library {lib_name}\nMonitor: {}",
                    session.monitor_string()
                );
            }
            st.add_to_engine(&mut eng).unwrap();
        }
        eprintln!("lib {lib_name} finished");
    });
}
