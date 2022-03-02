use serde::Serialize;

use crate::engine::{Engine, Result};

#[derive(Debug, Clone, Serialize)]
pub(crate) enum Sentence {
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
        if let Some(r) = s.strip_prefix("Todo ") {
            if let Some((name, body)) = r.split_once(":") {
                return Sentence::Todo {
                    name: name.trim().to_string(),
                    ty: body.to_string(),
                };
            }
        }
        if let Some(r) = s.strip_prefix("Axiom ") {
            if let Some((name, body)) = r.split_once(":") {
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
            if let Some((name, body)) = r.split_once(":") {
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
        match self {
            Sentence::Import { name } => engine.load_library(name)?,
            Sentence::Todo { name, ty }
            | Sentence::Axiom { name, ty }
            | Sentence::Theorem { name, ty, .. } => engine.add_axiom(name, ty)?,
        }
        Ok(())
    }

    pub(crate) fn name(&self) -> &str {
        let (Sentence::Import { name }
        | Sentence::Todo { name, .. }
        | Sentence::Axiom { name, .. }
        | Sentence::Theorem { name, .. }) = self;
        name
    }

    pub(crate) fn ty(&self) -> Option<&str> {
        match self {
            Sentence::Import { .. } => None,
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
