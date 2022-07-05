use hakim_engine::engine::Engine;

fn main() {
    let eng = Engine::default();
    let mut session = eng.interactive_session("forall a b: U, forall f: forall x: a, b, forall x y: a, forall p: eq a x y, eq b (f x) (f y)").unwrap();
    let mut rl = rustyline::Editor::<()>::new();
    loop {
        session.print();
        let line = match rl.readline("input tactic: ") {
            Ok(l) => l,
            Err(_) => break,
        };
        match session.run_tactic(&line) {
            Ok(_) => (),
            Err(e) => println!("Tactic Error: {:#?}", e),
        }
        if session.is_finished() {
            break;
        }
    }
}
