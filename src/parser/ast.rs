use std::collections::HashMap;

use crate::{
    app, app_ref,
    brain::{Term, TermRef},
    term, term_ref,
};

use super::tokenizer::{Keyword, Token};

#[derive(Debug)]
pub enum AstTerm {
    Forall {
        name: String,
        ty: Box<AstTerm>,
        body: Box<AstTerm>,
    },
    Ident(String),
    App(Box<AstTerm>, Box<AstTerm>),
    Number(u32),
}

use AstTerm::*;

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedEOF,
    ExpectedIdentButGot(Token),
    ExpectedSignButGot(String, Token),
    ExpectedExprButGot(Token),
}

use Error::*;

type Result<T> = std::result::Result<T, Error>;

trait TokenEater {
    fn peek_token(&self) -> Result<Token>;
    fn eat_token(&mut self) -> Result<Token>;

    fn eat_ident(&mut self) -> Result<String> {
        let t = self.peek_token()?;
        if let Token::Ident(s) = t {
            self.eat_token()?;
            Ok(s)
        } else {
            Err(ExpectedIdentButGot(t.clone()))
        }
    }

    fn eat_sign(&mut self, sign: &str) -> Result<()> {
        let t = self.peek_token()?;
        if let Token::Sign(s) = t {
            if s == sign {
                self.eat_token()?;
                Ok(())
            } else {
                Err(ExpectedSignButGot(sign.to_string(), Token::Sign(s)))
            }
        } else {
            Err(ExpectedSignButGot(sign.to_string(), t.clone()))
        }
    }

    fn eat_ast_without_app(&mut self) -> Result<AstTerm> {
        match self.peek_token()? {
            Token::Ident(s) => {
                let ident = Ident(s);
                self.eat_token()?;
                Ok(ident)
            }
            Token::Kw(kw) => match kw {
                Keyword::Forall => {
                    self.eat_token()?;
                    let name = self.eat_ident()?;
                    self.eat_sign(":")?;
                    let ty = Box::new(self.eat_ast()?);
                    self.eat_sign(",")?;
                    let body = Box::new(self.eat_ast()?);
                    Ok(Forall { name, ty, body })
                }
            },
            Token::Sign(s) => match s.as_str() {
                "(" => {
                    self.eat_token()?;
                    let r = self.eat_ast()?;
                    self.eat_sign(")")?;
                    Ok(r)
                }
                _ => Err(ExpectedExprButGot(Token::Sign(s))),
            },
            Token::Number(x) => {
                self.eat_token()?;
                Ok(Number(x))
            }
        }
    }

    fn eat_ast(&mut self) -> Result<AstTerm> {
        let mut v = vec![self.eat_ast_without_app()?];
        loop {
            let t = match self.peek_token() {
                Ok(k) => k,
                Err(err) => {
                    if err == UnexpectedEOF {
                        break;
                    } else {
                        return Err(err);
                    }
                }
            };
            if let Token::Sign(s) = t {
                if s != "(" {
                    break;
                }
            }
            v.push(self.eat_ast_without_app()?);
        }
        let mut iter = v.into_iter();
        let mut r = iter.next().unwrap();
        for x in iter {
            r = AstTerm::App(Box::new(r), Box::new(x));
        }
        Ok(r)
    }
}

impl TokenEater for &[Token] {
    fn peek_token(&self) -> Result<Token> {
        Ok(self.get(0).ok_or(Error::UnexpectedEOF)?.clone())
    }

    fn eat_token(&mut self) -> Result<Token> {
        let t = self.peek_token()?.clone();
        *self = &self[1..];
        Ok(t)
    }
}

pub fn tokens_to_ast(mut tokens: &[Token]) -> AstTerm {
    match tokens.eat_ast() {
        Ok(ast) => {
            if !tokens.is_empty() {
                panic!("Parse was ok but some tokens remained: {:?}", tokens);
            }
            ast
        },
        Err(err) => panic!("Error in parsing: {:?}. Tokens remain: {:?}", err, tokens),
    }
}

pub fn ast_to_term(
    ast: AstTerm,
    globals: &HashMap<String, TermRef>,
    name_stack: &mut Vec<String>,
) -> TermRef {
    match ast {
        Forall { name, ty, body } => {
            let ty_term = ast_to_term(*ty, globals, name_stack);
            name_stack.push(name);
            let body_term = ast_to_term(*body, globals, name_stack);
            name_stack.pop();
            TermRef::new(Term::Forall {
                var_ty: ty_term,
                body: body_term,
            })
        }
        Ident(s) => {
            if let Some(i) = name_stack.iter().rev().position(|x| *x == s) {
                return term_ref!(v i);
            }
            if let Some(t) = globals.get(&s) {
                t.clone()
            } else {
                panic!("name {} is undefined", s);
            }
        }
        App(a, b) => app_ref!(
            ast_to_term(*a, globals, name_stack),
            ast_to_term(*b, globals, name_stack)
        ),
        Number(num) => {
            let num_i32 = num as i32;
            term_ref!(n num_i32)
        },
    }
}
