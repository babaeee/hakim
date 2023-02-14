use im::HashMap;

use crate::engine::{Engine, Error, Result};

pub use self::text::all_names;
use self::{
    ast::{File, Sentence},
    text::load_text,
};

pub mod prelude;
mod text;

pub use text::LIB_TEXT_STORE;

mod ast;
#[cfg(test)]
mod tests;

fn load_library_by_text(engine: &mut Engine, text: &str) -> Result<()> {
    ast::File::parse(text).add_to_engine(engine)?;
    Ok(())
}

pub fn load_library_by_name(engine: &mut Engine, name: &str) -> Result<()> {
    let text = text_of_name(name)?;
    load_library_by_text(engine, &text)
}

fn text_of_name(name: &str) -> Result<String> {
    load_text(name).ok_or_else(|| Error::UnknownLibrary(name.to_string()))
}

pub(crate) fn proof_of_theorem(lib: &str, name: &str) -> Option<Vec<String>> {
    let lib = File::parse(&text_of_name(lib).ok()?);
    let x = lib.0.into_iter().find(|x| x.name() == Some(name))?;
    if let Sentence::Theorem { proof, .. } = x {
        Some(proof)
    } else {
        None
    }
}

pub(crate) fn engine_from_middle_of_lib(lib: &str, name: &str) -> Option<(Engine, String)> {
    let mut eng = Engine::default();
    let lib = File::parse(&text_of_name(lib).ok()?);
    for x in lib.0 {
        if x.name() == Some(name) {
            return Some((eng, x.ty()?.to_string()));
        }
        x.add_to_engine(&mut eng).ok()?;
    }
    None
}

pub fn all_library_data() -> HashMap<String, ast::File> {
    fn f(name: String, r: &mut HashMap<String, ast::File>) -> Result<()> {
        if r.contains_key(&name) {
            return Ok(());
        }
        let x = ast::File::parse(&text_of_name(&name)?);
        r.insert(name, x);
        Ok(())
    }
    let mut r = HashMap::new();
    for x in all_names() {
        f(x.to_string(), &mut r).unwrap();
    }
    r
}
