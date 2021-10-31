use std::cmp::max;

use super::{
    tokenizer::{AbsSign, Token},
    Error::*,
    Result,
};

use crate::{
    app_ref,
    brain::{increase_foreign_vars, TermRef},
    library::prelude::ex,
    parser::binop::{Assoc, BinOp},
    term_ref,
};

#[derive(Debug)]
pub enum AstTerm {
    Abs {
        sign: AbsSign,
        name: Vec<String>,
        ty: Box<AstTerm>,
        body: Box<AstTerm>,
    },
    Ident(String),
    App(Box<AstTerm>, Box<AstTerm>),
    BinOp(Box<AstTerm>, BinOp, Box<AstTerm>),
    Number(BigInt),
    Wild(usize),
}

use num_bigint::BigInt;
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
            Token::Abs(sign) => {
                self.eat_token()?;
                let name = self.eat_ident_vec()?;
                self.eat_sign(":")?;
                let ty = Box::new(self.eat_ast()?);
                self.eat_sign(",")?;
                let body = Box::new(self.eat_ast()?);
                Ok(Abs {
                    sign,
                    name,
                    ty,
                    body,
                })
            }
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
        fn build_ast(a: AstTerm, op: BinOp, b: AstTerm) -> AstTerm {
            if op == BinOp::App {
                App(Box::new(a), Box::new(b))
            } else {
                BinOp(Box::new(a), op, Box::new(b))
            }
        }
        fn push_to_stack(stack: &mut Vec<(AstTerm, BinOp)>, op: BinOp, mut n: AstTerm) {
            while let Some((_, op2)) = stack.last() {
                if op2.prec() > op.prec() {
                    break;
                }
                if op2.prec() == op.prec() && op.assoc() == Assoc::Right {
                    break;
                }
                let (n2, op2) = stack.pop().unwrap();
                n = build_ast(n2, op2, n);
            }
            stack.push((n, op));
        }
        let mut cur = self.eat_ast_without_app()?;
        let mut stack: Vec<(AstTerm, BinOp)> = vec![];
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
                if let Some(op) = BinOp::from_str(&s) {
                    self.eat_token()?;
                    push_to_stack(&mut stack, op, cur);
                    cur = self.eat_ast_without_app()?;
                    continue;
                }
                if s == "(" {
                    push_to_stack(&mut stack, BinOp::App, cur);
                    cur = self.eat_ast_without_app()?;
                    continue;
                }
                break;
            }
            push_to_stack(&mut stack, BinOp::App, cur);
            cur = self.eat_ast_without_app()?;
        }
        for (t, op) in stack.into_iter().rev() {
            cur = build_ast(t, op, cur);
        }
        Ok(cur)
    }
}

impl TokenEater for &[Token] {
    fn peek_token(&self) -> Result<Token> {
        Ok(self.get(0).ok_or(UnexpectedEOF)?.clone())
    }

    fn eat_token(&mut self) -> Result<Token> {
        let t = self.peek_token()?;
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

pub fn pack_abstraction(sign: AbsSign, ty: TermRef, body: TermRef) -> TermRef {
    match sign {
        AbsSign::Forall => term_ref!(forall ty, body),
        AbsSign::Fun => term_ref!(fun ty, body),
        AbsSign::Exists => app_ref!(ex(), ty, term_ref!(fun ty, body)),
    }
}

pub fn ast_to_term(
    ast: AstTerm,
    globals: &im::HashMap<String, TermRef>,
    name_stack: &mut Vec<String>,
    infer_cnt: &mut usize,
) -> Result<TermRef> {
    match ast {
        Abs {
            sign,
            name,
            ty,
            body,
        } => {
            let mut ty_term = ast_to_term(*ty, globals, name_stack, infer_cnt)?;
            let mut tys = vec![];
            for n in name {
                tys.push(ty_term.clone());
                ty_term = increase_foreign_vars(ty_term, 0);
                name_stack.push(n);
            }
            let mut r = ast_to_term(*body, globals, name_stack, infer_cnt)?;
            for ty in tys.into_iter().rev() {
                name_stack.pop();
                r = pack_abstraction(sign, ty, r);
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
            ast_to_term(*a, globals, name_stack, infer_cnt)?,
            ast_to_term(*b, globals, name_stack, infer_cnt)?
        )),
        Number(num) => Ok(term_ref!(n num)),
        Wild(i) => {
            *infer_cnt = max(*infer_cnt, i + 1);
            Ok(term_ref!(_ i))
        }
        BinOp(a, op, b) => {
            let ta = ast_to_term(*a, globals, name_stack, infer_cnt)?;
            let tb = ast_to_term(*b, globals, name_stack, infer_cnt)?;
            Ok(op.run_on_term(ta, tb))
        }
    }
}
