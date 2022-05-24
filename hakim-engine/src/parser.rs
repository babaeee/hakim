mod ast;
mod binop;
mod pretty_print;
mod span_counter;
mod tokenizer;
mod uniop;
mod wild;

use std::ops::Sub;

pub use self::ast::{ast_to_term, AstTerm};
pub use self::binop::BinOp;
pub use self::pretty_print::{term_pretty_print, term_to_ast};
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
    InvalidUniverseIndex(String),
    RemainTokens(Vec<Token>),
}

type Result<T> = std::result::Result<T, Error>;

pub fn parse(text: &str) -> Result<AstTerm> {
    let tokens = tokenize(text).unwrap();
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

#[cfg(test)]
mod tests;
