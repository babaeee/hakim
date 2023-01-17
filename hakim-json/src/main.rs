use hakim_json_lib::{run_command, State};
use std::panic::catch_unwind;

#[no_mangle]
fn exec_command(input: *const i8) -> *const i8 {
    use std::{
        cell::Cell,
        ffi::{CStr, CString},
    };

    thread_local! {
        static STATE: Cell<State> = Cell::new(State::default());
    }
    let command = serde_json::from_str(unsafe { CStr::from_ptr(input) }.to_str().unwrap()).unwrap();
    let state = STATE.with(|s| s.take());
    let result = catch_unwind(|| {
        let mut state = state;
        let r = run_command(command, &mut state);
        (state, r)
    });
    let result = match result {
        Ok((next_state, r)) => {
            STATE.with(|s| s.set(next_state));
            r
        }
        Err(_) => "panic".to_string(),
    };
    CString::new(result).unwrap().into_raw()
}

fn main() {}
