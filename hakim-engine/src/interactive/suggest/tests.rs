use crate::interactive::{
    tests::{run_interactive, EngineLevel},
    Session,
};

use super::{SuggClass, Suggestion};

#[derive(Debug)]
struct SuggRec {
    class: SuggClass,
    ans: Vec<String>,
}

impl SuggRec {
    fn vc<const N: usize>(f: [SuggClass; N]) -> Vec<SuggRec> {
        f.into_iter()
            .map(|x| SuggRec {
                class: x,
                ans: vec![],
            })
            .collect()
    }

    fn run_sugg(self, sugg: Suggestion, mut session: Session) {
        let SuggRec { class, ans } = self;
        if sugg.class != class {
            panic!("bad sugg class: expected {:?}\nSugg:{:?}", class, sugg);
        }
        let e = session.run_suggestion(sugg, ans.into_iter().collect());
        match e {
            Ok(_) => (),
            Err(e) => {
                panic!(
                    "failed to run sugg. Error: {:?}\nMonitor:\n{}",
                    e,
                    session.monitor_string()
                );
            }
        }
    }
}

fn check_hyp_menu(goal: &str, tactics: &str, hyp: &str, recs: Vec<SuggRec>, level: EngineLevel) {
    let session = run_interactive(goal, tactics, level);
    let sugg = session.suggest_on_hyp_menu(hyp);
    if sugg.len() != recs.len() {
        panic!(
            "Different suggestion count. Suggs:\n{:?}\nExpecteds:\n{:?}",
            sugg, recs
        );
    }
    for (s, r) in sugg.into_iter().zip(recs.into_iter()) {
        r.run_sugg(s, session.clone());
    }
}

fn check_goal_dblclk(goal: &str, tactics: &str, rec: SuggRec) {
    let session = run_interactive(goal, tactics, EngineLevel::Full);
    let sugg = session.suggest_on_goal_dblclk().unwrap();
    rec.run_sugg(sugg, session);
}

#[test]
fn exist_paran() {
    check_goal_dblclk(
        "∀ a: ℤ, ∃ b: ℤ, a < b",
        r#"
            intros a
            "#,
        SuggRec {
            class: SuggClass::Destruct,
            ans: vec!["a + 1".to_string()],
        },
    );
}

#[test]
fn exist_goal() {
    check_goal_dblclk(
        "∀ P: ℤ -> U, (∀ x: ℤ, P x -> P (2*x)) -> (∃ b: ℤ, P b) -> ∃ b: ℤ, P (2*b)",
        r#"
            intros P px_p2x exP
            apply (ex_ind ? ? exP)
            intros exP_value exP_proof
            "#,
        SuggRec {
            class: SuggClass::Destruct,
            ans: vec!["exP_value".to_string()],
        },
    );
}

#[test]
fn eq_hyp() {
    check_hyp_menu(
        "∀ x0: U, ∀ x1: U, ∀ x2: x0 → x1, ∀ x3: x0, ∀ x4: x0, eq x0 x3 x4 → eq x1 (x2 x3) (x2 x4)",
        r#"
            intros A B f a1 a2 eqa1a2
            "#,
        "eqa1a2",
        SuggRec::vc([SuggClass::Rewrite, SuggClass::Pattern("a = b", "b = a")]),
        EngineLevel::Full,
    );
    check_hyp_menu(
        "2 = 3 -> 3 = 2",
        r#"
            intros eq_2_3
            "#,
        "eq_2_3",
        SuggRec::vc([SuggClass::Rewrite]),
        EngineLevel::Empty,
    );
}

#[test]
fn set_hyp() {
    check_hyp_menu(
        "∀ t: U, ∀ s: set t, ∀ a b: t, a ∈ {b} -> a = b",
        r#"
            intros t s a b in_set_proof
            "#,
        "in_set_proof",
        SuggRec::vc([SuggClass::Pattern("a ∈ {b}", "a = b")]),
        EngineLevel::Full,
    );
}
