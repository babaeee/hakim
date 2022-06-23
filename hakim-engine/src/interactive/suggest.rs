use std::fmt::Display;

#[cfg(test)]
mod tests;

mod hyp;
pub use hyp::{suggest_on_hyp, suggest_on_hyp_dblclk};
mod goal;
pub use goal::{suggest_on_goal, suggest_on_goal_dblclk};

#[derive(PartialEq, Eq, Debug, Clone, Serialize, Deserialize)]
pub enum SuggClass {
    Intros,
    IntrosWithName,
    Destruct,
    DestructWithName,
    Rewrite,
    Contradiction,
    Instantiate,
    Trivial,
    Pattern(String, String),
}

impl SuggClass {
    #[cfg(test)]
    fn pattern(a: &str, b: &str) -> Self {
        Self::Pattern(a.to_string(), b.to_string())
    }
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
            Trivial => write!(f, "$trivial"),
            Pattern(a, b) => write!(f, "{a} ⇒ {b}"),
        }
    }
}

use serde::{Deserialize, Serialize};
use SuggClass::*;

use super::Frame;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum Applicablity {
    Normal,
    /// star it so it will go on dbl click
    Default,
    /// use in automatic proof in addition to dbl clicks
    Auto,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggRule {
    pub class: SuggClass,
    pub tactic: String,
    pub applicablity: Applicablity,
}

impl From<SuggRule> for Suggestion {
    fn from(sugg: SuggRule) -> Self {
        Self {
            class: sugg.class,
            tactic: sugg.tactic,
            questions: vec![],
            applicablity: sugg.applicablity,
        }
    }
}

impl SuggRule {
    fn try_on_goal(&self, frame: Frame) -> Option<Suggestion> {
        frame.run_tactic(&self.tactic).ok()?;
        Some(self.clone().into())
    }

    fn try_on_hyp(&self, name: &str, frame: Frame) -> Option<Suggestion> {
        frame.run_tactic(&self.tactic.replace("$n", name)).ok()?;
        let mut r: Suggestion = self.clone().into();
        r.tactic = r.tactic.replace("$n", name);
        Some(r)
    }
}

#[derive(Debug)]
pub struct Suggestion {
    pub class: SuggClass,
    pub tactic: String,
    pub questions: Vec<String>,
    pub applicablity: Applicablity,
}

impl Suggestion {
    fn new_default(class: SuggClass, t: &str) -> Self {
        Self {
            class,
            tactic: t.to_string(),
            questions: vec![],
            applicablity: Applicablity::Default,
        }
    }

    fn newq1default(class: SuggClass, t: &str, q: &str) -> Self {
        Self {
            class,
            tactic: t.to_string(),
            questions: vec![q.to_string()],
            applicablity: Applicablity::Default,
        }
    }

    pub fn is_default(&self) -> bool {
        matches!(
            self.applicablity,
            Applicablity::Default | Applicablity::Auto
        )
    }
}
