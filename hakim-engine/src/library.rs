use im::HashMap;

use crate::engine::{Engine, Error, Result};

use self::text::load_text;

pub mod prelude;
mod text;

mod ast;
#[cfg(test)]
mod tests;

fn load_library_by_text(engine: &mut Engine, text: &str) -> Result<()> {
    ast::File::parse(text).add_to_engine(engine)?;
    Ok(())
}

pub fn load_library_by_name(engine: &mut Engine, name: &str) -> Result<()> {
    let text = text_of_name(name)?;
    load_library_by_text(engine, text)
}

fn text_of_name(name: &str) -> Result<&str> {
    load_text(name).ok_or_else(|| Error::UnknownLibrary(name.to_string()))
}

pub fn all_library_data() -> HashMap<String, ast::File> {
    fn f(name: String, r: &mut HashMap<String, ast::File>) -> Result<()> {
        let x = ast::File::parse(text_of_name(&name)?);
        r.insert(name, x);
        Ok(())
    }
    let mut r = HashMap::new();
    f("All".to_string(), &mut r).unwrap();
    r
}
