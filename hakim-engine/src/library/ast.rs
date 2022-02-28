use serde::Serialize;

use crate::engine::{Engine, Result};

#[derive(Debug, Clone, Serialize)]
enum Sentence {
    Import { name: String },
    Axiom { name: String, ty: String },
}

impl Sentence {
    fn parse(s: &str) -> Self {
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
        todo!()
    }

    fn add_to_engine(&self, engine: &mut Engine) -> Result<()> {
        match self {
            Sentence::Import { name } => engine.load_library(name)?,
            Sentence::Axiom { name, ty } => engine.add_axiom(name, ty)?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct File(Vec<Sentence>);

fn split_by_sentence(text: &str) -> impl Iterator<Item = &str> {
    text.split('.').map(|x| x.trim()).filter(|x| !x.is_empty())
}

impl File {
    pub fn parse(text: &str) -> Self {
        Self(split_by_sentence(text).map(Sentence::parse).collect())
    }

    pub fn add_to_engine(&self, engine: &mut Engine) -> Result<()> {
        for x in self.0.iter() {
            x.add_to_engine(engine)?;
        }
        Ok(())
    }
}
