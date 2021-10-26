use self::interactive::Session;
use crate::{
    brain::{self, type_of, TermRef},
    library::{load_library_by_name, prelude},
    parser::{self, ast_to_term, is_valid_ident, parse},
    term_ref,
};

#[derive(Debug, Clone)]
pub struct Engine {
    name_dict: im::HashMap<String, TermRef>,
}

#[cfg(test)]
mod tests;

impl Default for Engine {
    fn default() -> Self {
        let mut name_dict: im::HashMap<String, TermRef> = Default::default();
        name_dict.insert("U".to_string(), prelude::u());
        name_dict.insert("U1".to_string(), prelude::u1());
        name_dict.insert("U2".to_string(), prelude::u2());
        name_dict.insert("U3".to_string(), prelude::u3());
        name_dict.insert("ℤ".to_string(), prelude::z());
        name_dict.insert("eq".to_string(), prelude::eq());
        name_dict.insert("eq_refl".to_string(), prelude::eq_refl());
        name_dict.insert("plus".to_string(), prelude::plus());
        name_dict.insert("mult".to_string(), prelude::mult());
        Self { name_dict }
    }
}

pub mod interactive;
mod tactic;

#[derive(Debug)]
pub enum Error {
    DuplicateName(String),
    InvalidIdentName(String),
    UnknownLibrary(String),
    InvalidSentence(String),
    ParserError(parser::Error),
    BrainError(brain::Error),
}

impl From<parser::Error> for Error {
    fn from(e: parser::Error) -> Self {
        ParserError(e)
    }
}

impl From<brain::Error> for Error {
    fn from(e: brain::Error) -> Self {
        BrainError(e)
    }
}

use Error::*;

pub type Result<T> = std::result::Result<T, Error>;

impl Engine {
    fn generate_name(&self, base: &str) -> String {
        if !self.name_dict.contains_key(base) {
            return base.to_string();
        }
        for i in 0.. {
            let n = format!("{}{}", base, i);
            if !self.name_dict.contains_key(&n) {
                return n;
            }
        }
        unreachable!();
    }

    fn add_name(&mut self, name: &str, term: TermRef) -> Result<()> {
        if !is_valid_ident(name) {
            return Err(InvalidIdentName(name.to_string()));
        }
        if self.name_dict.contains_key(name) {
            return Err(DuplicateName(name.to_string()));
        }
        self.name_dict.insert(name.to_string(), term);
        Ok(())
    }

    fn add_axiom_with_term(&mut self, name: &str, term: TermRef) -> Result<()> {
        let axiom = term_ref!(axiom name, term);
        self.add_name(name, axiom)
    }

    pub fn add_axiom(&mut self, name: &str, ty: &str) -> Result<()> {
        let parsed = self.parse_text(ty)?;
        type_of(parsed.clone()).unwrap();
        self.add_axiom_with_term(name, parsed)
    }

    pub fn calc_type(&self, text: &str) -> Result<TermRef> {
        let exp = self.parse_text(text)?;
        let ty = type_of(exp)?;
        Ok(ty)
    }

    pub fn load_library(&mut self, name: &str) -> Result<()> {
        load_library_by_name(self, name)
    }

    pub fn parse_text(&self, text: &str) -> Result<TermRef> {
        let ast = parse(text)?;
        let mut name_stack = vec![];
        let term = ast_to_term(ast, &self.name_dict, &mut name_stack)?;
        Ok(term)
    }

    pub fn interactive_session(&self, goal: &str) -> Result<Session> {
        Session::new(self.clone(), goal)
    }
}
