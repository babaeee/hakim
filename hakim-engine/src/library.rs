use crate::engine::{self, Engine, Error};

use self::text::load_text;

pub mod prelude;
mod text;

#[cfg(test)]
mod tests;

fn split_by_sentence(text: &str) -> impl Iterator<Item = &str> {
    text.split(".").map(|x| x.trim()).filter(|x| !x.is_empty())
}

fn run_sentence(engine: &mut Engine, s: &str) -> engine::Result<()> {
    if let Some(r) = s.strip_prefix("Axiom ") {
        if let Some((name, body)) = r.split_once(":") {
            return engine.add_axiom(name.trim(), body);
        }
    }
    Err(Error::InvalidSentence(s.to_string()))
}

fn load_library_by_text(engine: &mut Engine, text: &str) -> engine::Result<()> {
    let sentences = split_by_sentence(text);
    for s in sentences {
        run_sentence(engine, s)?;
    }
    Ok(())
}

pub fn load_library_by_name(engine: &mut Engine, name: &str) -> engine::Result<()> {
    let text = load_text(name).ok_or(Error::UnknownLibrary(name.to_string()))?;
    load_library_by_text(engine, text)
}
