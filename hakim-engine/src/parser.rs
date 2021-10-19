mod ast;
mod tokenizer;

pub use self::ast::{AstTerm, ast_to_term};

use self::{ast::{tokens_to_ast}, tokenizer::{Token, tokenize}};


#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedEOF,
    ExpectedIdentButGot(Token),
    ExpectedSignButGot(String, Token),
    ExpectedExprButGot(Token),
    UndefinedName(String),
    RemainTokens(Vec<Token>),
}

type Result<T> = std::result::Result<T, Error>;

pub fn parse(text: &str) -> Result<AstTerm> {
    let tokens = tokenize(text).unwrap();
    tokens_to_ast(&tokens)
}
