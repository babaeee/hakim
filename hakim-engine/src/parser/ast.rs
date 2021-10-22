use super::{Error::*, Result};

use crate::{
    app_ref,
    brain::{increase_foreign_vars, Term, TermRef},
    term_ref,
};

use super::tokenizer::{Keyword, Token};

#[derive(Debug)]
pub enum AstTerm {
    Forall {
        name: Vec<String>,
        ty: Box<AstTerm>,
        body: Box<AstTerm>,
    },
    Ident(String),
    App(Box<AstTerm>, Box<AstTerm>),
    Number(u32),
    Wild(usize),
}

use AstTerm::*;

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

    fn eat_ident_vec(&mut self) -> Result<Vec<String>> {
        let mut v = vec![];
        while let Token::Ident(s) = self.peek_token()? {
            self.eat_token()?;
            v.push(s);
        }
        Ok(v)
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
            Token::Wild(i) => {
                let t = Wild(i);
                self.eat_token()?;
                Ok(t)
            }
            Token::Kw(kw) => match kw {
                Keyword::Forall => {
                    self.eat_token()?;
                    let name = self.eat_ident_vec()?;
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
        Ok(self.get(0).ok_or(UnexpectedEOF)?.clone())
    }

    fn eat_token(&mut self) -> Result<Token> {
        let t = self.peek_token()?.clone();
        *self = &self[1..];
        Ok(t)
    }
}

pub fn tokens_to_ast(mut tokens: &[Token]) -> Result<AstTerm> {
    let ast = tokens.eat_ast()?;
    if tokens.is_empty() {
        Ok(ast)
    } else {
        Err(RemainTokens(tokens.to_vec()))
    }
}

pub fn ast_to_term(
    ast: AstTerm,
    globals: &im::HashMap<String, TermRef>,
    name_stack: &mut Vec<String>,
) -> Result<TermRef> {
    match ast {
        Forall { name, ty, body } => {
            let mut ty_term = ast_to_term(*ty, globals, name_stack)?;
            let mut tys = vec![];
            for n in name {
                tys.push(ty_term.clone());
                ty_term = increase_foreign_vars(ty_term, 0);
                name_stack.push(n);
            }
            let mut r = ast_to_term(*body, globals, name_stack)?;
            for ty in tys.into_iter().rev() {
                name_stack.pop();
                r = TermRef::new(Term::Forall {
                    body: r,
                    var_ty: ty,
                });
            }
            Ok(r)
        }
        Ident(s) => {
            if let Some(i) = name_stack.iter().rev().position(|x| *x == s) {
                return Ok(term_ref!(v i));
            }
            if let Some(t) = globals.get(&s) {
                Ok(t.clone())
            } else {
                Err(UndefinedName(s))
            }
        }
        App(a, b) => Ok(app_ref!(
            ast_to_term(*a, globals, name_stack)?,
            ast_to_term(*b, globals, name_stack)?
        )),
        Number(num) => {
            let num_i32 = num as i32;
            Ok(term_ref!(n num_i32))
        }
        Wild(i) => Ok(term_ref!(_ i)),
    }
}
