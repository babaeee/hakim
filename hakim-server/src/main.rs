use std::{
    panic,
    sync::{
        mpsc::{channel, Receiver, Sender},
        Mutex,
    },
    thread,
    time::SystemTime,
};

use actix_cors::Cors;
use actix_web::{post, web, App, HttpServer, Responder};
use hakim_json_lib::{run_command, Command, State};
use serde_json::Value;

#[post("/")]
async fn hello(
    state: web::Data<Mutex<(Sender<Value>, Receiver<String>)>>,
    command: web::Json<Value>,
) -> impl Responder {
    let (command_p, answer_n) = &mut *state.lock().unwrap();
    command_p.send(command.clone()).unwrap();
    answer_n.recv().unwrap()
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    if open::that("https://proof.babaeee.ir").is_err() {
        println!("Failed to open https://proof.babaeee.ir due some error. Open it manually.");
    }
    let (command_p, command_n) = channel();
    let (answer_p, answer_n) = channel();
    thread::spawn(move || {
        let mut state = State::default();
        static HISTORY: Mutex<String> = Mutex::new(String::new());
        panic::set_hook(Box::new(|info| {
            println!("Got panic. @info: {}", info);
            let _ = std::fs::write(
                format!(
                    "hakim_log_{}.log",
                    SystemTime::now()
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .unwrap()
                        .as_millis()
                ),
                &*HISTORY.lock().unwrap(),
            );
            std::process::abort();
        }));
        loop {
            let command: Value = command_n.recv().unwrap();
            {
                let mut h = HISTORY.lock().unwrap();
                h.push_str(&serde_json::to_string(&command).unwrap());
                h.push('\n');
            }
            dbg!(&command);
            let command: Command = serde_json::from_value(command).unwrap();
            dbg!(&command);
            let result = run_command(command, &mut state);
            dbg!(&result);
            {
                let mut h = HISTORY.lock().unwrap();
                h.push_str(&result);
                h.push('\n');
            }
            answer_p.send(result).unwrap();
        }
    });
    let state = web::Data::new(Mutex::new((command_p, answer_n)));
    HttpServer::new(move || {
        App::new()
            .app_data(state.clone())
            .service(hello)
            .wrap(Cors::permissive())
    })
    .bind(("127.0.0.1", 9438))?
    .run()
    .await
}
