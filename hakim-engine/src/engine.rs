use std::collections::HashMap;

use super::interactive::Session;
use crate::{
    brain::{
        self,
        infer::{type_of_and_infer, InferResults},
        normalize, predict_axiom, type_of, Term, TermRef,
    },
    interactive::SuggRule,
    library::{all_names, load_library_by_name, prelude},
    parser::{self, ast_to_term, fix_wild_scope, is_valid_ident, parse, term_pretty_print},
    search::search,
    term_ref,
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Engine {
    name_dict: im::HashMap<String, TermRef>,
    libs: im::HashMap<String, ()>,
    pub params: im::HashMap<String, String>,
    pub hyp_suggs: im::Vector<SuggRule>,
    pub goal_suggs: im::Vector<SuggRule>,
}

#[derive(Debug)]
pub enum Error {
    DuplicateName(String),
    InvalidIdentName(String),
    UnknownLibrary(String),
    InvalidSentence(String),
    ParserError(parser::Error),
    BrainError(brain::Error),
    InvalidTypeForAxiom(String),
    GoalWithWildCard(TermRef),
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

use serde::{Deserialize, Serialize};
use Error::*;

pub type Result<T> = std::result::Result<T, Error>;

impl Default for Engine {
    fn default() -> Self {
        Self::new("")
    }
}

impl Engine {
    pub fn new(params: &str) -> Self {
        let name_dict = prelude::init_dict();
        let libs = im::HashMap::<String, ()>::default();
        let hyp_suggs = im::Vector::default();
        let goal_suggs = im::Vector::default();
        let params = params
            .split('&')
            .filter_map(|x| x.trim().split_once('='))
            .map(|(x, y)| (x.to_owned(), y.to_owned()))
            .collect();
        Self {
            name_dict,
            libs,
            params,
            hyp_suggs,
            goal_suggs,
        }
    }

    pub fn generate_name(&self, base: &str) -> String {
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

    pub fn lib_iter(&self) -> impl Iterator<Item = (&str, TermRef)> {
        self.name_dict.iter().filter_map(|(a, t)| {
            let ty = type_of(t.clone()).ok()?;
            Some((a.as_str(), ty))
        })
    }

    pub fn remove_name_unchecked(&mut self, name: &str) {
        self.name_dict.remove(name).unwrap();
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

    pub fn add_axiom_with_term(&mut self, name: &str, term: TermRef) -> Result<()> {
        let term = normalize(term);
        let ty = type_of(term.clone())?;
        if !matches!(ty.as_ref(), Term::Universe { index: _ }) {
            return Err(InvalidTypeForAxiom(name.to_string()));
        }
        let axiom = term_ref!(axiom name, term);
        self.add_name(name, axiom)
    }

    pub fn add_axiom(&mut self, name: &str, ty: &str) -> Result<()> {
        let parsed = self.parse_text(ty)?;
        self.add_axiom_with_term(name, parsed)
    }

    pub fn calc_type(&self, text: &str) -> Result<TermRef> {
        let exp = self.parse_text(text)?;
        let ty = type_of(exp)?;
        Ok(normalize(ty))
    }

    pub fn load_library(&mut self, name: &str) -> Result<()> {
        for lib in all_names() {
            if lib.starts_with(name) {
                self.load_library_single(lib)?;
            }
        }
        Ok(())
    }

    pub fn load_library_single(&mut self, name: &str) -> Result<()> {
        if self.has_library(name) {
            return Ok(());
        }
        load_library_by_name(self, name)?;
        self.libs.insert(name.to_string(), ());
        Ok(())
    }

    pub fn check(&self, query: &str) -> Result<String> {
        let term = self.parse_text(query)?;
        let ty = type_of(term)?;
        Ok(self.pretty_print(&ty))
    }

    pub fn search(&self, query: &str) -> Result<Vec<String>> {
        search(self, query)
    }

    pub fn parse_text_with_wild(&self, text: &str) -> Result<(TermRef, usize)> {
        let ast = parse(text)?;
        let mut name_stack = vec![];
        let mut infer_cnt = Default::default();
        let term = ast_to_term(
            ast,
            &self.name_dict,
            &mut name_stack,
            &mut HashMap::default(),
            &mut infer_cnt,
        )?;
        let n = infer_cnt.0;
        let term = fix_wild_scope(term, n);
        // check if all axioms in the generated term are registered in the engine
        predict_axiom(&term, |x| {
            if !self.name_dict.contains_key(x) {
                panic!("invalid axiom {x} in the parsed term");
            }
            true
        });
        Ok((term, n))
    }

    pub fn parse_text(&self, text: &str) -> Result<TermRef> {
        let (term, infer_cnt) = self.parse_text_with_wild(text)?;
        let mut infers = InferResults::new(infer_cnt);
        let ty = type_of_and_infer(term.clone(), &mut infers)?;
        type_of_and_infer(ty, &mut infers)?;
        let term = infers.fill(term);
        Ok(term)
    }

    pub fn interactive_session(&self, goal: &str) -> Result<Session> {
        Session::new(self.clone(), goal)
    }

    pub(crate) fn has_library(&self, arg: &str) -> bool {
        self.libs.contains_key(arg)
    }

    pub fn pretty_print(&self, term: &Term) -> String {
        term_pretty_print(term, |x| !self.name_dict.contains_key(x))
    }

    pub(crate) fn type_of_name(&self, name: &str) -> Result<TermRef> {
        let x = self.parse_text(name)?;
        Ok(type_of(x)?)
    }

    pub(crate) fn add_hyp_sugg(&mut self, sugg: SuggRule) {
        self.hyp_suggs.push_back(sugg);
    }

    pub(crate) fn add_goal_sugg(&mut self, sugg: SuggRule) {
        self.goal_suggs.push_back(sugg);
    }

    pub(crate) fn is_disabled_tactic(&self, name: &str) -> bool {
        self.params
            .get("disabled_tactics")
            .unwrap_or(&String::new())
            .split(',')
            .any(|x| x.trim() == name)
    }
}
