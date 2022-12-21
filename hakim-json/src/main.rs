use std::panic::catch_unwind;

use hakim_engine::{
    all_library_data,
    engine::Engine,
    interactive::{tactic, Session, Suggestion},
    notation_list,
};

#[cfg(target_arch = "wasm32")]
use hakim_engine::library::LIB_TEXT_STORE;

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
#[serde(tag = "command", content = "arg")]
#[serde(rename_all = "snake_case")]
enum Command {
    ToBackup,
    FromBackup(State),
    StartSession {
        goal: String,
        libs: String,
        params: String,
    },
    #[cfg(target_arch = "wasm32")]
    LoadLib(std::collections::HashMap<String, String>),
    NotationList,
    Monitor,
    AllLibraryData,
    Natural,
    TryAuto,
    TryAutoHistory,
    GetHistory,
    RunTactic(String),
    SuggestDblclkGoal,
    SuggestDblclkHyp(String),
    SuggestMenuGoal,
    SuggestMenuHyp(String),
    RunSuggestMenuGoal(usize),
    RunSuggestMenuHyp {
        hyp_name: String,
        index: usize,
    },
    AnswerQuestion(String),
    Search(String),
    Check(String),
    ActionOfTactic(String),
    TryTactic(String),
}

use Command::*;

#[derive(Default, Serialize, Deserialize)]
struct State {
    session: Option<Session>,
    question: Option<QuestionState>,
}

fn serialize(s: impl Serialize) -> String {
    serde_json::to_string(&s).unwrap()
}

const DONE: Option<&str> = None;

#[derive(Serialize, Deserialize)]
struct Error(String);

#[derive(Serialize, Deserialize)]
enum AskQuestionHolder {
    AskQuestion(String),
}

use AskQuestionHolder::AskQuestion;

#[derive(Serialize, Deserialize)]
struct Panic;

#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum UntaggedEither<A, B> {
    Left(A),
    Right(B),
}

#[derive(Serialize, Deserialize)]
enum QuestionState {
    ForTactic(tactic::FindInstance),
    ForSuggestion {
        suggestion: Suggestion,
        answers: Vec<String>,
    },
}

#[no_mangle]
fn exec_command(input: *const i8) -> *const i8 {
    use std::{
        cell::Cell,
        ffi::{CStr, CString},
    };

    thread_local! {
        static STATE: Cell<State> = Cell::new(State { session: None, question: None });
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
        Err(_) => serialize(Panic),
    };
    CString::new(result).unwrap().into_raw()
}

fn main() {}

fn run_command(command: Command, state: &mut State) -> String {
    if state.question.is_some() && !matches!(command, AnswerQuestion(_)) {
        panic!("Unanswered question");
    }
    match command {
        ToBackup => serialize(&state),
        FromBackup(s) => {
            *state = s;
            serialize(DONE)
        }
        StartSession { goal, libs, params } => {
            let mut eng = Engine::new(&params);
            for lib in libs.split(',') {
                if let Err(e) = eng.load_library(lib) {
                    return serialize(Error(format!("{:?}", e)));
                }
            }
            state.session = match eng.interactive_session(&goal) {
                Ok(s) => Some(s),
                Err(e) => {
                    return serialize(Error(format!("{:?}", e)));
                }
            };
            serialize(DONE)
        }
        #[cfg(target_arch = "wasm32")]
        LoadLib(lib) => {
            LIB_TEXT_STORE.with(|x| *x.borrow_mut() = lib);
            serialize(DONE)
        }
        NotationList => serialize(notation_list()),
        Monitor => serialize(state.session.as_ref().map(|s| s.monitor(true))),
        AllLibraryData => serialize(all_library_data()),
        Natural => serialize(state.session.as_ref().map(|s| s.natural())),
        TryAuto => serialize(state.session.as_ref().and_then(|s| s.try_auto())),
        TryAutoHistory => serialize(state.session.as_ref().and_then(|s| s.history_based_auto())),
        GetHistory => serialize(state.session.as_ref().map(|s| s.get_history())),
        RunTactic(tactic) => serialize(run_tactic(state, tactic)),
        SuggestDblclkGoal => {
            let session = match &mut state.session {
                Some(s) => s,
                None => return serialize("session not started"),
            };
            let sugg = match session.suggest_on_goal_dblclk() {
                Some(s) => s,
                None => return serialize("No suggestion for this type of goal"),
            };
            serialize(run_sugg(state, sugg, vec![]))
        }
        SuggestDblclkHyp(hyp) => {
            let session = match &mut state.session {
                Some(s) => s,
                None => return serialize("session not started"),
            };
            let sugg = match session.suggest_on_hyp_dblclk(&hyp) {
                Some(s) => s,
                None => return serialize("No suggestion for this type of hyp"),
            };
            serialize(run_sugg(state, sugg, vec![]))
        }
        SuggestMenuGoal => serialize(
            state
                .session
                .as_ref()
                .map(|s| sugg_menu(s.suggest_on_goal_menu())),
        ),
        SuggestMenuHyp(hyp) => serialize(
            state
                .session
                .as_ref()
                .map(|s| sugg_menu(s.suggest_on_hyp_menu(&hyp))),
        ),
        RunSuggestMenuGoal(i) => {
            let session = match &mut state.session {
                Some(s) => s,
                None => return serialize("session not started"),
            };
            let sugg = session.suggest_on_goal_menu().into_iter().nth(i).unwrap();
            serialize(run_sugg(state, sugg, vec![]))
        }
        RunSuggestMenuHyp { hyp_name, index } => {
            let session = match &mut state.session {
                Some(s) => s,
                None => return serialize("session not started"),
            };
            let sugg = session
                .suggest_on_hyp_menu(&hyp_name)
                .into_iter()
                .nth(index)
                .unwrap();
            serialize(run_sugg(state, sugg, vec![]))
        }
        AnswerQuestion(answer) => match state.question.take().expect("Unexpected answer") {
            QuestionState::ForTactic(e) => {
                let qt = e.question_text();
                match e.tactic_by_answer(&answer) {
                    Ok(t) => match run_tactic(state, t) {
                        UntaggedEither::Left(Some(er)) => {
                            serialize(AskQuestion(format!("$error: {er}\n{qt}")))
                        }
                        rest => serialize(rest),
                    },
                    Err(er) => serialize(AskQuestion(format!("$error: {er:?}\n{qt}"))),
                }
            }
            QuestionState::ForSuggestion {
                suggestion,
                mut answers,
            } => {
                answers.push(answer);
                serialize(run_sugg(state, suggestion, answers))
            }
        },
        Check(query) => serialize({
            let eng = if let Some(s) = &state.session {
                s.initial_engine()
            } else {
                return "No session".to_string();
            };
            match eng.check(&query) {
                Ok(r) => r,
                Err(e) => format!("{:?}", e),
            }
        }),
        Search(query) => {
            let eng = if let Some(s) = &state.session {
                s.initial_engine()
            } else {
                return serialize("No session");
            };
            match eng.search(&query) {
                Ok(r) => {
                    let x = r
                        .into_iter()
                        .map(|x| {
                            let ty = eng.calc_type_and_infer(&x).unwrap();
                            (x, eng.pretty_print(&ty))
                        })
                        .collect::<Vec<_>>();
                    serialize(x)
                }
                Err(e) => serialize(&format!("{:?}", e)),
            }
        }
        ActionOfTactic(tactic) => {
            serialize(state.session.as_mut().unwrap().action_of_tactic(&tactic))
        }
        TryTactic(tactic) => serialize(state.session.as_ref().unwrap().try_tactic(&tactic)),
    }
}

fn sugg_menu(suggs: Vec<Suggestion>) -> String {
    suggs
        .into_iter()
        .map(|x| {
            if x.is_default() {
                format!("(★{})", x.class)
            } else {
                format!("({})", x.class)
            }
        })
        .collect()
}

fn run_tactic(
    state: &mut State,
    tactic: String,
) -> UntaggedEither<Option<String>, AskQuestionHolder> {
    use UntaggedEither::*;
    let session = match &mut state.session {
        Some(s) => s,
        None => return Left(Some("session not started".into())),
    };
    match session.run_tactic(&tactic) {
        Ok(_) => Left(None),
        Err(tactic::Error::CanNotFindInstance(e)) => {
            let qt = e.question_text();
            state.question = Some(QuestionState::ForTactic(*e));
            Right(AskQuestion(qt))
        }
        Err(e) => Left(Some(format!("{:?}", e))),
    }
}

fn run_sugg(
    state: &mut State,
    sugg: Suggestion,
    answers: Vec<String>,
) -> UntaggedEither<Option<String>, AskQuestionHolder> {
    use UntaggedEither::*;
    let session = match &mut state.session {
        Some(s) => s,
        None => return Left(Some("session not started".into())),
    };
    if let Some(q) = sugg.questions.get(answers.len()) {
        let q = q.clone();
        state.question = Some(QuestionState::ForSuggestion {
            suggestion: sugg,
            answers,
        });
        return Right(AskQuestion(q));
    }
    match session.run_suggestion(sugg, answers) {
        Ok(_) => Left(None),
        Err(e) => Left(Some(format!("{:?}", e))),
    }
}
