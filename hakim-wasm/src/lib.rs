use serde::{Deserialize, Serialize};
use std::panic;

use hakim_engine::{
    engine::Engine,
    interactive::{Session, Suggestion},
};
use wasm_bindgen::prelude::*;

// When the `wee_alloc` feature is enabled, use `wee_alloc` as the global
// allocator.
#[cfg(feature = "wee_alloc")]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[wasm_bindgen]
extern "C" {
    fn panic_handler(s: &str);
    fn ask_question(s: &str) -> String;
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
        panic::set_hook(Box::new(|p| {
            panic_handler(&format!(
                "Panic on rust side. This is a bug. The page \
        will no longer work properly. Reload the page.\n\nMore data:\n{}",
                p
            ))
        }));
    });
}

#[derive(Serialize, Deserialize)]
enum Monitor {
    SessionIsNotStarted,
    Finished,
    Monitor {
        hyps: Vec<(String, String)>,
        goals: Vec<String>,
    },
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
    pub fn monitor(&self) -> JsValue {
        let monitor = match &self.session {
            Some(s) if s.is_finished() => Monitor::Finished,
            Some(s) => {
                let mut snapshot = s.last_snapshot().clone();
                let goals = snapshot
                    .frames
                    .iter()
                    .map(|x| format!("{:?}", x.goal))
                    .collect();
                let hyps = snapshot
                    .pop_frame()
                    .hyps
                    .into_iter()
                    .map(|(k, v)| (k, format!("{:?}", v)))
                    .collect();
                Monitor::Monitor { goals, hyps }
            }
            None => Monitor::SessionIsNotStarted,
        };
        JsValue::from_serde(&monitor).unwrap()
    }

    pub fn try_auto(&self) -> Option<String> {
        let s = (&self.session)
            .as_ref()?
            .last_snapshot()
            .clone()
            .pop_frame();
        let tac = if s.run_tactic("ring").ok().filter(|x| x.is_empty()).is_some() {
            "ring"
        } else {
            return None;
        };
        Some(tac.to_string())
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

    fn run_sugg(&mut self, sugg: Suggestion) -> Option<String> {
        let session = match &mut self.session {
            Some(s) => s,
            None => return Some("Session is not started".to_string()),
        };
        let v = sugg.questions.iter().map(|x| ask_question(x)).collect();
        match session.run_suggestion(sugg, v) {
            Ok(_) => None,
            Err(e) => Some(format!("{:?}", e)),
        }
    }

    pub fn suggest_dblclk_goal(&mut self) -> Option<String> {
        let session = match &mut self.session {
            Some(s) => s,
            None => return Some("Session is not started".to_string()),
        };
        let sugg = match session.suggest_on_goal_dblclk() {
            Some(s) => s,
            None => return Some("No suggestion for this type of goal".to_string()),
        };
        self.run_sugg(sugg)
    }

    pub fn suggest_dblclk_hyp(&mut self, hyp_name: &str) -> Option<String> {
        let session = match &mut self.session {
            Some(s) => s,
            None => return Some("Session is not started".to_string()),
        };
        let sugg = match session.suggest_on_hyp_dblclk(hyp_name) {
            Some(s) => s,
            None => return Some("No suggestion for this type of hyp".to_string()),
        };
        self.run_sugg(sugg)
    }

    pub fn search(&self, query: &str) -> String {
        match self.engine.search(query) {
            Ok(r) => r
                .into_iter()
                .map(|x| {
                    let ty = self.engine.calc_type(&x).unwrap();
                    format!("{}: {:?}\n", x, ty)
                })
                .collect(),
            Err(e) => format!("{:?}", e),
        }
    }
}
