#![allow(clippy::unused_unit)]
use async_recursion::async_recursion;
use backtrace::Backtrace;
use js_sys::Promise;
use serde::{Deserialize, Serialize};
use std::panic;
use wasm_bindgen_futures::future_to_promise;

use hakim_engine::{
    engine::Engine,
    interactive::{tactic::Error, Session, Suggestion},
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
    async fn ask_question(s: &str) -> JsValue;
}

#[wasm_bindgen]
#[derive(Default, Serialize, Deserialize)]
pub struct Instance {
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
        will no longer work properly. Reload the page.\n\nMore data:\n{}\nBacktrace:\n{:?}",
                p,
                Backtrace::new(),
            ))
        }));
    });
}

#[derive(Serialize, Deserialize)]
enum Monitor {
    SessionIsNotStarted,
    Finished,
    Running {
        hyps: Vec<(String, String)>,
        goals: Vec<String>,
    },
}

#[async_recursion(?Send)]
async fn run_tactic_inner(session: &mut Session, tactic: &str) -> Option<String> {
    match session.run_tactic(tactic) {
        Ok(_) => None,
        Err(Error::CanNotFindInstance(e)) => {
            if let Some(ans) = ask_question(&e.question_text()).await.as_string() {
                run_tactic_inner(session, &e.tactic_by_answer(&ans).ok()?).await
            } else {
                Some("bad output of ask_question".to_string())
            }
        }
        Err(e) => Some(format!("{:?}", e)),
    }
}

#[wasm_bindgen]
impl Instance {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        start();
        Instance { session: None }
    }

    #[wasm_bindgen]
    pub fn to_backup(&self) -> JsValue {
        let serializer = serde_wasm_bindgen::Serializer::json_compatible();
        self.serialize(&serializer).unwrap()
    }

    #[wasm_bindgen]
    pub fn from_backup(&mut self, json: JsValue) -> bool {
        match serde_wasm_bindgen::from_value(json) {
            Ok(x) => {
                *self = x;
                true
            }
            Err(_) => false,
        }
    }

    #[wasm_bindgen]
    pub fn start_session(&mut self, goal: &str, libs: &str) -> Option<String> {
        let mut eng = Engine::default();
        for lib in libs.split(',') {
            if let Err(e) = eng.load_library(lib) {
                return Some(format!("{:?}", e));
            }
        }
        self.session = match eng.interactive_session(goal) {
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
                    .map(|x| x.engine.pretty_print(&x.goal))
                    .collect();
                let hyps = {
                    let frame = snapshot.pop_frame();
                    frame
                        .hyps
                        .into_iter()
                        .map(|(k, v)| (k, frame.engine.pretty_print(&v)))
                        .collect()
                };
                Monitor::Running { goals, hyps }
            }
            None => Monitor::SessionIsNotStarted,
        };
        serde_wasm_bindgen::to_value(&monitor).unwrap()
    }

    pub fn try_auto(&self) -> Option<String> {
        let mut s = (&self.session).as_ref()?.last_snapshot().clone();
        if s.is_finished() {
            return None;
        }
        let s = s.pop_frame();
        let mut r = None;
        const AUTO_TAC: [&str; 3] = ["ring", "auto_set", "lia"];
        for tac in AUTO_TAC {
            if s.run_tactic(tac).ok().filter(|x| x.is_empty()).is_some() {
                r = Some(tac.to_string());
                break;
            }
        }
        r
    }

    pub fn try_tactic(&self, tactic: &str) -> bool {
        let session = match &self.session {
            Some(s) => s,
            None => return false,
        };
        match session.clone().run_tactic(tactic) {
            Ok(_) => true,
            Err(e) => e.is_actionable(),
        }
    }

    #[wasm_bindgen]
    pub fn run_tactic(&mut self, tactic: String) -> Promise {
        let this = unsafe { std::mem::transmute::<&mut Instance, &'static mut Instance>(self) };
        future_to_promise(async move {
            let session = match &mut this.session {
                Some(s) => s,
                None => return Ok("session not started".into()),
            };
            let r = run_tactic_inner(session, &tactic).await;
            Ok(r.into())
        })
    }

    #[wasm_bindgen]
    pub fn get_history(&self) -> JsValue {
        let session = match &self.session {
            Some(s) => s,
            None => return JsValue::UNDEFINED,
        };
        serde_wasm_bindgen::to_value(&session.get_history()).unwrap()
    }

    async fn run_sugg(&mut self, sugg: Suggestion) -> Option<String> {
        let session = match &mut self.session {
            Some(s) => s,
            None => return Some("Session is not started".to_string()),
        };
        let mut v = vec![];
        for x in &sugg.questions {
            let x = match ask_question(x).await.as_string() {
                Some(x) => x,
                None => return Some("invalid question type".to_string()),
            };
            v.push(x);
        }
        match session.run_suggestion(sugg, v) {
            Ok(_) => None,
            Err(e) => Some(format!("{:?}", e)),
        }
    }

    pub fn suggest_dblclk_goal(&mut self) -> Promise {
        let this = unsafe { std::mem::transmute::<&mut Instance, &'static mut Instance>(self) };
        future_to_promise(async move {
            let session = match &mut this.session {
                Some(s) => s,
                None => return Ok("Session is not started".into()),
            };
            let sugg = match session.suggest_on_goal_dblclk() {
                Some(s) => s,
                None => return Ok("No suggestion for this type of goal".into()),
            };
            Ok(this.run_sugg(sugg).await.into())
        })
    }

    pub fn suggest_dblclk_hyp(&mut self, hyp_name: String) -> Promise {
        let this = unsafe { std::mem::transmute::<&mut Instance, &'static mut Instance>(self) };
        future_to_promise(async move {
            let session = match &mut this.session {
                Some(s) => s,
                None => return Ok("Session is not started".into()),
            };
            let sugg = match session.suggest_on_hyp_dblclk(&hyp_name) {
                Some(s) => s,
                None => return Ok("No suggestion for this type of hyp".into()),
            };
            Ok(this.run_sugg(sugg).await.into())
        })
    }

    pub fn suggest_menu_goal(&mut self) -> Option<String> {
        let session = &mut self.session.as_ref()?;
        let sugg = session.suggest_on_goal_menu();
        Some(
            sugg.into_iter()
                .map(|x| {
                    if x.is_default {
                        format!("(★{:?})", x.class)
                    } else {
                        format!("({:?})", x.class)
                    }
                })
                .collect(),
        )
    }

    pub fn suggest_menu_hyp(&mut self, hyp_name: &str) -> Option<String> {
        let session = &mut self.session.as_ref()?;
        let sugg = session.suggest_on_hyp_menu(hyp_name);
        Some(
            sugg.into_iter()
                .map(|x| {
                    if x.is_default {
                        format!("(★{:?})", x.class)
                    } else {
                        format!("({:?})", x.class)
                    }
                })
                .collect(),
        )
    }

    pub fn run_suggest_menu_hyp(&mut self, hyp_name: String, i: usize) -> Promise {
        let this = unsafe { std::mem::transmute::<&mut Instance, &'static mut Instance>(self) };
        future_to_promise(async move {
            let session = match &mut this.session {
                Some(s) => s,
                None => return Ok("Session is not started".into()),
            };
            let sugg = session.suggest_on_hyp_menu(&hyp_name);
            Ok(this
                .run_sugg(
                    sugg.into_iter()
                        .nth(i)
                        .ok_or("Bug in run_suggest_menu_hyp")?,
                )
                .await
                .into())
        })
    }

    pub fn run_suggest_menu_goal(&mut self, i: usize) -> Promise {
        let this = unsafe { std::mem::transmute::<&mut Instance, &'static mut Instance>(self) };
        future_to_promise(async move {
            let session = match &mut this.session {
                Some(s) => s,
                None => return Ok("Session is not started".into()),
            };
            let sugg = session.suggest_on_goal_menu();
            Ok(this
                .run_sugg(
                    sugg.into_iter()
                        .nth(i)
                        .ok_or("Bug in run_suggest_menu_goal")?,
                )
                .await
                .into())
        })
    }

    pub fn search(&self, query: &str) -> String {
        let eng = if let Some(s) = &self.session {
            s.initial_engine()
        } else {
            return "No session".to_string();
        };
        match eng.search(query) {
            Ok(r) => r
                .into_iter()
                .map(|x| {
                    let ty = eng.calc_type(&x).unwrap();
                    format!("{}: {:?}\n", x, ty)
                })
                .collect(),
            Err(e) => format!("{:?}", e),
        }
    }
}
