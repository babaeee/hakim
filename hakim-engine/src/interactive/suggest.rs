use std::fmt::Display;

#[cfg(test)]
mod tests;

mod hyp;
pub use hyp::{suggest_on_hyp, suggest_on_hyp_dblclk};
mod goal;
pub use goal::{suggest_on_goal, suggest_on_goal_dblclk};

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum SuggClass {
    Intros,
    IntrosWithName,
    Destruct,
    DestructWithName,
    Rewrite,
    Contradiction,
    Instantiate,
    Pattern(&'static str, &'static str),
}

impl Display for SuggClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Intros => write!(f, "$intros"),
            IntrosWithName => write!(f, "$intros_with_name"),
            Destruct => write!(f, "$destruct"),
            DestructWithName => write!(f, "$destruct_with_name"),
            Rewrite => write!(f, "$rewrite"),
            Contradiction => write!(f, "$contradiction"),
            Instantiate => write!(f, "$instantiate"),
            Pattern(a, b) => write!(f, "{a} ⇒ {b}"),
        }
    }
}

use SuggClass::*;

use super::Frame;

#[derive(Debug, Clone, Copy)]
pub struct SuggRule {
    pub class: SuggClass,
    pub tactic: &'static [&'static str],
    pub questions: &'static [&'static str],
    pub is_default: bool,
}

impl From<SuggRule> for Suggestion {
    fn from(sugg: SuggRule) -> Self {
        Self {
            class: sugg.class,
            tactic: sugg.tactic.iter().map(|x| x.to_string()).collect(),
            questions: sugg.questions.iter().map(|x| x.to_string()).collect(),
            is_default: sugg.is_default,
        }
    }
}

impl SuggRule {
    fn try_on_goal(self, frame: Frame) -> Option<Suggestion> {
        frame.run_tactic(self.tactic[0]).ok()?;
        Some(self.into())
    }

    fn try_on_hyp(self, name: &str, frame: Frame) -> Option<Suggestion> {
        frame.run_tactic(&self.tactic[0].replace("$n", name)).ok()?;
        let mut r: Suggestion = self.into();
        r.tactic = r
            .tactic
            .into_iter()
            .map(|x| x.replace("$n", name))
            .collect();
        Some(r)
    }
}

#[derive(Debug)]
pub struct Suggestion {
    pub class: SuggClass,
    pub tactic: Vec<String>,
    pub questions: Vec<String>,
    pub is_default: bool,
}

impl Suggestion {
    fn new_default(class: SuggClass, t: &str) -> Self {
        Self {
            class,
            tactic: vec![t.to_string()],
            questions: vec![],
            is_default: true,
        }
    }

    fn newq1default(class: SuggClass, t: &str, q: &str) -> Self {
        Self {
            class,
            tactic: vec![t.to_string()],
            questions: vec![q.to_string()],
            is_default: true,
        }
    }
}
