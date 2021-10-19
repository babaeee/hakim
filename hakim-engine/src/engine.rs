use std::collections::HashMap;
use crate::{app_ref, brain::{self, Term, TermRef, type_of}, parser::{self, ast_to_term, parse}, term_ref};
use self::interactive::InteractiveSession;

pub struct Engine {
    name_dict: HashMap<String, TermRef>,
}

#[cfg(test)]
mod tests;

impl Default for Engine {
    fn default() -> Self {
        let mut name_dict: HashMap<String, TermRef> = Default::default();
        let u = term_ref!(universe 0);
        let nat = term_ref!(axiom "nat" , u);
        let v0 = term_ref!(v 0);
        let v1 = term_ref!(v 1);
        let eq = term_ref!(axiom "eq" , forall u, forall v0, forall v1, u);
        let eq_refl = term_ref!(axiom "eq_refl" , forall u, forall v0, app_ref!(eq, v1, v0, v0));
        name_dict.insert("U".to_string(), u);
        name_dict.insert("nat".to_string(), nat);
        name_dict.insert("eq".to_string(), eq);
        name_dict.insert("eq_refl".to_string(), eq_refl);
        Self { name_dict }
    }
}

pub mod interactive;
mod tactic;

#[derive(Debug)]
pub enum Error {
    DuplicateName(String),
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

type Result<T> = std::result::Result<T, Error>;

impl Engine {
    fn add_name(&mut self, name: &str, term: TermRef) -> Result<()> {
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
        type_of(dbg!(parsed.clone())).unwrap();
        self.add_axiom_with_term(name, parsed)
    }

    pub fn calc_type(&self, text: &str) -> Result<TermRef> {
        let exp = self.parse_text(text)?;
        let ty = type_of(exp)?;
        Ok(ty)
    }

    fn parse_text(&self, text: &str) -> Result<TermRef> {
        let ast = parse(text)?;
        let mut name_stack = vec![];
        let term = ast_to_term(ast, &self.name_dict, &mut name_stack)?;
        Ok(term)
    }

    pub fn interactive_session<'a>(&'a mut self, goal: &str) -> Result<InteractiveSession<'a>> {
        InteractiveSession::new(self, goal)
    }
}
