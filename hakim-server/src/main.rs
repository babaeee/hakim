use std::{
    sync::{
        mpsc::{channel, Receiver, Sender},
        Mutex,
    },
    thread,
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
    let (command_p, command_n) = channel();
    let (answer_p, answer_n) = channel();
    thread::spawn(move || {
        let mut state = State::default();
        loop {
            let command: Value = command_n.recv().unwrap();
            dbg!(&command);
            let command: Command = serde_json::from_value(command).unwrap();
            dbg!(&command);
            let result = run_command(command, &mut state);
            dbg!(&result);
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
