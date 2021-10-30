use crate::interactive::tests::run_interactive;

use super::SuggClass;

fn check_goal_dblclk(goal: &str, tactics: &str, class: SuggClass, ans: Vec<&str>) {
    let mut session = run_interactive(goal, tactics);
    let sugg = session.suggest_on_goal_dblclk().unwrap();
    if sugg.class != class {
        panic!("bad sugg class: expected {:?}\nSugg:{:?}", class, sugg);
    }
    let e = session.run_suggestion(sugg, ans.into_iter().map(|x| x.to_owned()).collect());
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

#[test]
fn exist_goal() {
    check_goal_dblclk(
        "∀ P: ℤ -> U, (∀ x: ℤ, P x -> P (2*x)) -> (∃ b: ℤ, P b) -> ∃ b: ℤ, P (2*b)",
        r#"
            intros P px_p2x exP
            apply ex_ind (3:=exP)
            intros exP_value exP_proof
            "#,
        SuggClass::Destruct,
        vec!["exP_value"],
    );
}
