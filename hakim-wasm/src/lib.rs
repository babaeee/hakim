use std::panic;

use hakim_engine::engine::{interactive::Session, Engine};
use wasm_bindgen::prelude::*;

// When the `wee_alloc` feature is enabled, use `wee_alloc` as the global
// allocator.
#[cfg(feature = "wee_alloc")]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);
}

#[wasm_bindgen]
#[derive(Default)]
pub struct Instance {
    engine: Engine,
    session: Option<Session>,
}

#[wasm_bindgen(start)]
pub fn start() {
    use std::sync::Once;
    static SET_HOOK: Once = Once::new();
    SET_HOOK.call_once(|| {
        panic::set_hook(Box::new(|_| {
            alert(
                "Panic on rust side. This is a bug. The page \
        will no longer work properly. Reload the page.",
            )
        }));
    });
}

#[wasm_bindgen]
impl Instance {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        start();
        let engine = Engine::default();
        Instance {
            engine,
            session: None,
        }
    }

    #[wasm_bindgen]
    pub fn load_library(&mut self, name: &str) -> Option<String> {
        if self.session.is_some() {
            return Some("Can not load library while session is alive".to_string());
        }
        match self.engine.load_library(name) {
            Ok(_) => None,
            Err(e) => Some(format!("{:?}", e)),
        }
    }

    #[wasm_bindgen]
    pub fn start_session(&mut self, goal: &str) -> Option<String> {
        self.session = match self.engine.interactive_session(goal) {
            Ok(s) => Some(s),
            Err(e) => return Some(format!("{:?}", e)),
        };
        None
    }

    #[wasm_bindgen]
    pub fn monitor(&self) -> String {
        let session = match &self.session {
            Some(s) => s,
            None => return "Session is not started".to_string(),
        };
        session.monitor_string()
    }

    #[wasm_bindgen]
    pub fn run_tactic(&mut self, tactic: &str) -> Option<String> {
        let session = match &mut self.session {
            Some(s) => s,
            None => return Some("session is not started".to_string()),
        };
        match session.run_tactic(tactic) {
            Ok(_) => None,
            Err(e) => Some(format!("{:?}", e)),
        }
    }

    #[wasm_bindgen]
    pub fn get_history(&self) -> JsValue {
        let session = match &self.session {
            Some(s) => s,
            None => return JsValue::UNDEFINED,
        };
        JsValue::from_serde(&session.get_history()).unwrap()
    }
}
