use clap::Parser;
use hakim_engine::engine::Engine;

#[derive(Parser)]
enum Command {
    Check { path: String },
    Interactive { goal: String },
}

fn main() {
    let mut eng = Engine::default();
    eng.load_library("/").unwrap();
    let command = Command::parse();
    match command {
        Command::Check { path } => {
            let text = std::fs::read_to_string(path).expect("Error in openning file");
            let mut commands = text.split(';').map(|x| x.trim());
            let goal = commands.next().unwrap().strip_prefix("Goal ").unwrap();
            let mut session = eng.interactive_session(goal).unwrap();
            for command in commands {
                if command == "Proof" || command.is_empty() {
                    continue;
                }
                match session.run_tactic(command) {
                    Ok(_) => (),
                    Err(e) => {
                        println!("Tactic Error: {:#?}", e);
                        return;
                    }
                }
            }
            if !session.is_finished() {
                println!("Proof is not finished");
                handle_session(session);
            }
        }
        Command::Interactive { goal } => {
            let session = eng.interactive_session(&goal).unwrap();
            handle_session(session);
        }
    }
}

fn handle_session(mut session: hakim_engine::interactive::Session) {
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
