use std::time::Duration;

use hakim_engine::{
    all_library_data,
    engine::Engine,
    interactive::{tactic, Session, Suggestion},
    notation_list,
};

#[cfg(feature = "z3")]
use hakim_engine::interactive::Z3_TIMEOUT;

use hakim_engine::library::LIB_TEXT_STORE;

use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "command", content = "arg")]
#[serde(rename_all = "snake_case")]
pub enum Command {
    ToBackup,
    FromBackup(State),
    StartSession {
        goal: String,
        libs: String,
        params: String,
    },
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
    PosOfSpanHyp {
        hyp: String,
        l: i32,
        r: i32,
    },
    PosOfSpanGoal {
        l: i32,
        r: i32,
    },
    AnswerQuestion(String),
    Search(String),
    Check(String),
    ActionOfTactic(String),
    TryTactic(String),
    ChangeZ3Timeout(u64),
    Z3Solved,
}

use Command::*;

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct State {
    session: Option<Session>,
    question: Option<QuestionState>,
}

const DONE: Option<&str> = None;

#[derive(Serialize, Deserialize)]
struct Error(String);

#[derive(Serialize, Deserialize)]
enum StateHolder {
    AskQuestion(String),
    Z3State(String),
}

use StateHolder::AskQuestion;
use StateHolder::Z3State;

#[derive(Serialize, Deserialize)]
struct Panic;

#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum UntaggedEither<A, B> {
    Left(A),
    Right(B),
}

#[derive(Debug, Serialize, Deserialize)]
enum QuestionState {
    ForTactic(tactic::FindInstance),
    ForSuggestion {
        suggestion: Suggestion,
        answers: Vec<String>,
    },
}

pub fn serialize(s: impl Serialize) -> String {
    serde_json::to_string(&s).unwrap()
}

pub fn run_command(command: Command, state: &mut State) -> String {
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
        LoadLib(lib) => {
            *LIB_TEXT_STORE.lock().unwrap() = Some(lib);
            serialize(DONE)
        }
        NotationList => serialize(notation_list()),
        Monitor => serialize(state.session.as_ref().map(|s| s.monitor(true))),
        AllLibraryData => serialize(all_library_data()),
        Natural => serialize(state.session.as_ref().map(|s| s.natural())),
        TryAuto => {
            let Some(s) = state.session.as_ref() else {
                return serialize(None::<String>);
            };
            if let Some(x) = s.try_auto() {
                serialize(x)
            } else {
                serialize(s.z3_get_state().map(Z3State))
            }
        }
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
        AnswerQuestion(answer) if answer.is_empty() => {
            // empty answer is equivalent to cancelling request
            state.question = None;
            "null".to_string()
        }
        AnswerQuestion(answer) => match state.question.take().expect("Unexpected answer") {
            QuestionState::ForTactic(e) => {
                let qt = e.question_text();
                match e.clone().tactic_by_answer(&answer) {
                    Ok(t) => match run_tactic(state, t) {
                        UntaggedEither::Left(Some(er)) => {
                            state.question = Some(QuestionState::ForTactic(e));
                            serialize(AskQuestion(format!("$error: {er}\n{qt}")))
                        }
                        rest => serialize(rest),
                    },
                    Err(er) => {
                        state.question = Some(QuestionState::ForTactic(e));
                        serialize(AskQuestion(format!("$error: {er:?}\n{qt}")))
                    }
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
                Err(e) => serialize(format!("{:?}", e)),
            }
        }
        ActionOfTactic(tactic) => {
            serialize(state.session.as_mut().unwrap().action_of_tactic(&tactic))
        }
        TryTactic(tactic) => serialize(state.session.as_ref().unwrap().try_tactic(&tactic)),
        PosOfSpanHyp { hyp, l, r } => {
            let Ok(l) = l.try_into() else {
                return serialize("negative bound");
            };
            let Ok(r) = r.try_into() else {
                return serialize("negative bound");
            };
            serialize(
                state
                    .session
                    .as_ref()
                    .unwrap()
                    .pos_of_span_hyp(&hyp, (l, r)),
            )
        }
        PosOfSpanGoal { l, r } => {
            let Ok(l) = l.try_into() else {
                return serialize("negative bound");
            };
            let Ok(r) = r.try_into() else {
                return serialize("negative bound");
            };
            serialize(state.session.as_ref().unwrap().pos_of_span_goal((l, r)))
        }
        ChangeZ3Timeout(t) => {
            //let mut g = Z3_TIMEOUT.lock().unwrap();
            //*g = Duration::from_millis(t);
            serialize(())
        }
        Z3Solved => {
            state.session.as_mut().map(|s| s.z3_solved());
            serialize(UntaggedEither::<Option<String>, StateHolder>::Left(None))
        }
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

fn run_tactic(state: &mut State, tactic: String) -> UntaggedEither<Option<String>, StateHolder> {
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
        Err(tactic::Error::Z3State(s)) => Right(Z3State(s)),
        Err(e) => Left(Some(format!("{:?}", e))),
    }
}

fn run_sugg(
    state: &mut State,
    sugg: Suggestion,
    answers: Vec<String>,
) -> UntaggedEither<Option<String>, StateHolder> {
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
