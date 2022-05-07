use serde::Serialize;

use crate::{
    engine::{Engine, Result},
    interactive::{SuggClass, SuggRule},
};

#[derive(Debug, Clone, Serialize)]
pub enum SuggTarget {
    Goal,
    Hyp,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) enum Sentence {
    Suggestion {
        target: SuggTarget,
        tactic: String,
        is_default: bool,
        class: SuggClass,
    },
    Import {
        name: String,
    },
    Axiom {
        name: String,
        ty: String,
    },
    Todo {
        name: String,
        ty: String,
    },
    Theorem {
        name: String,
        ty: String,
        proof: Vec<String>,
    },
}

impl Sentence {
    fn parse<'a, T: Iterator<Item = &'a str> + 'a>(it: &mut T) -> Self {
        let s = it.next().unwrap();
        if let Some(mut r) = s.strip_prefix("Suggest ") {
            let target = if let Some(x) = r.strip_prefix("goal ") {
                r = x;
                SuggTarget::Goal
            } else if let Some(x) = r.strip_prefix("hyp ") {
                r = x;
                SuggTarget::Hyp
            } else {
                panic!("invalid type for suggestion");
            };
            let is_default = if let Some(x) = r.strip_prefix("default ") {
                r = x;
                true
            } else {
                false
            };
            let tactic = match r.split_once(';') {
                Some((t, rest)) => {
                    r = rest;
                    t.to_string()
                }
                None => panic!("missing semicolon in suggestion"),
            };
            let class = match r.split_once("=>") {
                Some((l, r)) => SuggClass::Pattern(l.trim().to_string(), r.trim().to_string()),
                None => match r.trim() {
                    "Destruct" => SuggClass::Destruct,
                    "Contradiction" => SuggClass::Contradiction,
                    "Rewrite" => SuggClass::Rewrite,
                    "intros" => SuggClass::Intros,
                    "Instantiate" => SuggClass::Instantiate,
                    _ => panic!("unknown sugg class {r}"),
                },
            };
            return Sentence::Suggestion {
                target,
                tactic,
                is_default,
                class,
            };
        }
        if let Some(r) = s.strip_prefix("Todo ") {
            if let Some((name, body)) = r.split_once(':') {
                return Sentence::Todo {
                    name: name.trim().to_string(),
                    ty: body.to_string(),
                };
            }
        }
        if let Some(r) = s.strip_prefix("Axiom ") {
            if let Some((name, body)) = r.split_once(':') {
                return Sentence::Axiom {
                    name: name.trim().to_string(),
                    ty: body.to_string(),
                };
            }
        }
        if let Some(r) = s.strip_prefix("Import ") {
            return Sentence::Import {
                name: r.to_string(),
            };
        }
        if let Some(r) = s.strip_prefix("Theorem ") {
            if let Some((name, body)) = r.split_once(':') {
                let mut proof = vec![];
                assert_eq!("Proof", it.next().unwrap());
                for x in it {
                    if x == "Qed" {
                        break;
                    }
                    proof.push(x.to_string());
                }
                return Sentence::Theorem {
                    name: name.trim().to_string(),
                    ty: body.to_string(),
                    proof,
                };
            }
        }
        panic!("invalid sentence {:?}", s);
    }

    pub(crate) fn add_to_engine(&self, engine: &mut Engine) -> Result<()> {
        match self.clone() {
            Sentence::Suggestion {
                target,
                tactic,
                is_default,
                class,
            } => {
                let sugg = SuggRule {
                    class,
                    tactic: vec![tactic],
                    is_default,
                };
                match target {
                    SuggTarget::Hyp => engine.add_hyp_sugg(sugg),
                    SuggTarget::Goal => engine.add_goal_sugg(sugg),
                }
            }
            Sentence::Import { name } => engine.load_library(&name)?,
            Sentence::Todo { name, ty }
            | Sentence::Axiom { name, ty }
            | Sentence::Theorem { name, ty, .. } => engine.add_axiom(&name, &ty)?,
        }
        Ok(())
    }

    pub(crate) fn name(&self) -> Option<&str> {
        if let Sentence::Import { name }
        | Sentence::Todo { name, .. }
        | Sentence::Axiom { name, .. }
        | Sentence::Theorem { name, .. } = self
        {
            Some(name)
        } else {
            None
        }
    }

    pub(crate) fn ty(&self) -> Option<&str> {
        match self {
            Sentence::Suggestion { .. } | Sentence::Import { .. } => None,
            Sentence::Todo { ty, .. }
            | Sentence::Axiom { ty, .. }
            | Sentence::Theorem { ty, .. } => Some(ty),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct File(pub(crate) Vec<Sentence>);

fn split_by_sentence(text: &str) -> impl Iterator<Item = &str> {
    text.split('.').map(|x| x.trim()).filter(|x| !x.is_empty())
}

impl File {
    pub fn parse(text: &str) -> Self {
        let mut it = split_by_sentence(text).peekable();
        let mut r = vec![];
        while it.peek().is_some() {
            r.push(Sentence::parse(&mut it));
        }
        Self(r)
    }

    pub fn add_to_engine(&self, engine: &mut Engine) -> Result<()> {
        for x in self.0.iter() {
            x.add_to_engine(engine)?;
        }
        Ok(())
    }
}
