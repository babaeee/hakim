use hakim_json_lib::{run_command, State};
use std::panic::catch_unwind;
use std::{
    cell::Cell,
    ffi::{CStr, CString},
};

fn exec_command_impl(input: &str) -> String {
    thread_local! {
        static STATE: Cell<State> = Cell::new(State::default());
    }
    let command = serde_json::from_str(input).unwrap();
    let state = STATE.with(|s| s.take());
    let result = catch_unwind(|| {
        let mut state = state;
        let r = run_command(command, &mut state);
        (state, r)
    });
    match result {
        Ok((next_state, r)) => {
            STATE.with(|s| s.set(next_state));
            r
        }
        Err(_) => "panic".to_string(),
    }
}

#[no_mangle]
fn exec_command(input: *const i8) -> *const i8 {
    let s = unsafe { CStr::from_ptr(input) }.to_str().unwrap();
    let result = exec_command_impl(s);
    CString::new(result).unwrap().into_raw()
}

#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    loop {
        let mut buf = String::new();
        std::io::stdin().read_line(&mut buf).unwrap();
        let result = exec_command_impl(&buf);
        println!("{result}");
    }
}
