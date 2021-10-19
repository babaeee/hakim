use hakim_engine::engine::Engine;

fn main() {
    /*let u = term_ref!(universe 0);
    let nat = term_ref!(axiom "nat" , u);
    let v0 = term_ref!(v 0);
    let v1 = term_ref!(v 1);
    let v2 = term_ref!(v 2);
    let v3 = term_ref!(v 3);
    let n1 = term_ref!(n 1);
    let n2 = term_ref!(n 2);
    let n3 = term_ref!(n 3);
    let plus = term_ref!(axiom "plus", forall nat, forall nat , nat);
    let eq = term_ref!(axiom "eq" , forall u , forall v0, forall v1, u);
    let plus_2_1 = app_ref!(plus, n2, n1);
    let eq_2_p_1_3 = term_ref!(axiom "eq_2p1_3", app_ref!(eq, nat, plus_2_1, n3));
    let eq_switch = term_ref!(axiom "eq_switch", forall u, forall v0, forall v1, forall app_ref!(eq, v2, v0, v1), app_ref!(eq, v3, v2, v1));
    println!("{:#?}", plus_2_1);
    println!("{:#?}", type_of(plus_2_1.clone()));
    println!("{:#?}", eq_2_p_1_3);
    println!("{:#?}", type_of(eq_2_p_1_3.clone()));
    println!("{:#?}", eq_switch);
    println!("{:#?}", type_of(eq_switch.clone()));
    println!(
        "{:#?}",
        type_of(app_ref!(app_ref!(eq_switch, nat, n3, plus_2_1), eq_2_p_1_3))
    );*/
    let mut eng = Engine::default();
    eng.add_axiom(
        "eq_switch",
        "forall t: U, forall x1: t, forall x2: t, forall p: eq t x1 x2, eq t x2 x1",
    )
    .unwrap();
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
    //println!("{:#?}", parse("forall x: nat, eq nat (plus x 24) 75"));
}
