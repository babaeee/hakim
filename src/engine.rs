use std::collections::HashMap;
use crate::{brain::{Term, TermRef, type_of}, parser::{ast_to_term, parse}, term, term_ref};
use super::parser::{AstTerm};

pub struct Engine {
    name_dict: HashMap<String, TermRef>,
}

impl Default for Engine {
    fn default() -> Self {
        let mut name_dict: HashMap<String, TermRef> = Default::default();
        name_dict.insert("U".to_string(), term_ref!(universe 0));
        name_dict.insert("nat".to_string(), term_ref!(axiom "nat" , universe 0));
        Self { name_dict }
    }
}

impl Engine {
    pub fn add_axiom(&mut self, name: &str, ty: &str) {
        let ty_ast = parse(ty);
        let parsed = self.parse_ast(ty_ast);
        type_of(dbg!(parsed.clone())).unwrap();
        let axiom = dbg!(term_ref!(axiom name, parsed));
        self.name_dict.insert(name.to_string(), axiom);
    }

    pub fn calc_type(&self, text: &str) -> TermRef {
        let ast = parse(text);
        let exp = self.parse_ast(ast);
        type_of(exp).unwrap()
    }

    fn parse_ast(&self, ast: AstTerm) -> TermRef {
        let mut name_stack = vec![];
        ast_to_term(ast, &self.name_dict, &mut name_stack)
    }
}
