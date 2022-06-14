mod ast;
mod binop;
mod pretty_print;
mod semantic_highlight;
mod span_counter;
mod tokenizer;
mod uniop;
mod wild;

use std::collections::HashSet;
use std::ops::Sub;

use crate::library::prelude::z;
use crate::term_ref;

pub use self::ast::{ast_to_term, AstTerm};
pub use self::binop::BinOp;
use self::binop::ALL_BINOPS;
#[cfg(test)]
pub use self::pretty_print::structural_print;
pub use self::pretty_print::{term_pretty_print, term_to_ast, PrettyPrintConfig};
pub use self::semantic_highlight::{HighlightTag, HtmlRenderer};
pub use self::span_counter::pos_of_span;
pub use self::tokenizer::{is_valid_ident, is_whity_char};
pub use self::wild::{fix_wild_scope, InferGenerator};

use self::{
    ast::tokens_to_ast,
    tokenizer::{tokenize, Token},
};

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedEOF,
    ExpectedIdentButGot(Token),
    ExpectedSignButGot(String, Token),
    ExpectedExprButGot(Token),
    UndefinedName(String),
    BadChar(char),
    InvalidUniverseIndex(String),
    RemainTokens(Vec<Token>),
    TokenizerError(String),
}

type Result<T> = std::result::Result<T, Error>;

pub struct ParserConfig {
    pub names_with_hidden_args: im::HashMap<String, usize>,
}

pub fn parse(text: &str) -> Result<AstTerm> {
    let tokens = tokenize(text.into()).map_err(Error::TokenizerError)?;
    tokens_to_ast(&tokens)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct PrecLevel(u8);

impl PrecLevel {
    const MAX: Self = PrecLevel(200);
}

impl Sub<u8> for PrecLevel {
    type Output = PrecLevel;

    fn sub(self, rhs: u8) -> Self::Output {
        Self(self.0 - rhs)
    }
}

pub fn notation_list() -> Vec<String> {
    ALL_BINOPS
        .iter()
        .map(|x| {
            let term = x.run_on_term(
                &mut InferGenerator::default(),
                term_ref!(axiom "A", z()),
                term_ref!(axiom "B", z()),
            );
            format!(
                "A {x} B = {}",
                term_pretty_print::<String, _>(
                    &term,
                    |_| true,
                    &PrettyPrintConfig {
                        disabled_binops: HashSet::from([*x]),
                        names_with_hidden_args: im::HashMap::default(),
                    }
                )
            )
        })
        .collect()
}

#[cfg(test)]
mod tests;
