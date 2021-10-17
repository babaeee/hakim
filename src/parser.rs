mod ast;
mod tokenizer;

pub use self::ast::{AstTerm, ast_to_term};

use self::{
    ast::{tokens_to_ast},
    tokenizer::tokenize,
};

pub fn parse(text: &str) -> AstTerm {
    let tokens = tokenize(text).unwrap();
    let ast = tokens_to_ast(&tokens);
    ast
}
