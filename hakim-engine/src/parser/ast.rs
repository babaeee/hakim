use std::collections::HashMap;

use super::{
    tokenizer::{AbsSign, Token},
    wild::InferGenerator,
    Error::*,
    Result,
};

use crate::{
    app_ref,
    brain::{increase_foreign_vars, Abstraction, Term, TermRef},
    library::prelude::{ex, set_empty, set_from_func, set_singleton, union},
    parser::binop::{Assoc, BinOp},
    term_ref,
};

#[derive(Debug)]
pub struct AstAbs {
    name: Vec<String>,
    ty: Box<AstTerm>,
    body: Box<AstTerm>,
}

#[derive(Debug)]
pub enum AstSet {
    Abs(AstAbs),
    Items(Vec<AstTerm>),
}

#[derive(Debug)]
pub enum AstTerm {
    Abs(AbsSign, AstAbs),
    Ident(String),
    App(Box<AstTerm>, Box<AstTerm>),
    BinOp(Box<AstTerm>, BinOp, Box<AstTerm>),
    Number(BigInt),
    Wild(Option<String>),
    Set(AstSet),
}

use num_bigint::BigInt;
use AstTerm::*;

trait TokenEater {
    fn eat_token(&mut self) -> Result<Token>;
    fn look_ahead(&self, i: usize) -> Result<Token>;

    fn peek_token(&self) -> Result<Token> {
        self.look_ahead(0)
    }

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

    fn eat_set(&mut self) -> Result<AstTerm> {
        // we already eated Sign("{")
        if self.look_ahead(1) == Ok(Token::Sign(":".to_string())) {
            let name = vec![self.eat_ident()?];
            self.eat_sign(":")?;
            let ty = Box::new(self.eat_ast_with_disallowed_sign(|x| x == "|")?);
            self.eat_sign("|")?;
            let body = Box::new(self.eat_ast()?);
            self.eat_sign("}")?;
            Ok(Set(AstSet::Abs(AstAbs { name, ty, body })))
        } else {
            let mut r = vec![];
            loop {
                if self.peek_token()? == Token::Sign("}".to_string()) {
                    self.eat_token()?;
                    break Ok(Set(AstSet::Items(r)));
                }
                r.push(self.eat_ast()?);
                if self.peek_token()? == Token::Sign("}".to_string()) {
                    self.eat_token()?;
                    break Ok(Set(AstSet::Items(r)));
                }
                self.eat_sign(",")?;
            }
        }
    }

    fn eat_ast_without_app(&mut self) -> Result<AstTerm> {
        match self.eat_token()? {
            Token::Ident(s) => {
                let ident = Ident(s);
                Ok(ident)
            }
            Token::Wild(i) => {
                let t = Wild(i);
                Ok(t)
            }
            Token::Abs(sign) => {
                let name = self.eat_ident_vec()?;
                self.eat_sign(":")?;
                let ty = Box::new(self.eat_ast()?);
                self.eat_sign(",")?;
                let body = Box::new(self.eat_ast()?);
                Ok(Abs(sign, AstAbs { name, ty, body }))
            }
            Token::Sign(s) => match s.as_str() {
                "(" => {
                    let r = self.eat_ast()?;
                    self.eat_sign(")")?;
                    Ok(r)
                }
                "{" => self.eat_set(),
                _ => Err(ExpectedExprButGot(Token::Sign(s))),
            },
            Token::Number(x) => Ok(Number(x)),
        }
    }

    fn eat_ast(&mut self) -> Result<AstTerm> {
        self.eat_ast_with_disallowed_sign(|_| false)
    }

    fn eat_ast_with_disallowed_sign(&mut self, disallow_sign: fn(&str) -> bool) -> Result<AstTerm> {
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
                if disallow_sign(&s) {
                    break;
                }
                if let Some(op) = BinOp::from_str(&s) {
                    self.eat_token()?;
                    push_to_stack(&mut stack, op, cur);
                    cur = self.eat_ast_without_app()?;
                    continue;
                }
                if s == "(" || s == "{" {
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
    fn look_ahead(&self, i: usize) -> Result<Token> {
        Ok(self.get(i).ok_or(UnexpectedEOF)?.clone())
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

pub fn pack_abstraction(sign: AbsSign, abs: Abstraction) -> TermRef {
    match sign {
        AbsSign::Forall => TermRef::new(Term::Forall(abs)),
        AbsSign::Fun => TermRef::new(Term::Fun(abs)),
        AbsSign::Exists => app_ref!(ex(), abs.var_ty, pack_abstraction(AbsSign::Fun, abs)),
    }
}

pub fn ast_to_term(
    ast: AstTerm,
    globals: &im::HashMap<String, TermRef>,
    name_stack: &mut Vec<String>,
    infer_dict: &mut HashMap<String, usize>,
    infer_cnt: &mut InferGenerator,
) -> Result<TermRef> {
    match ast {
        Set(AstSet::Abs(AstAbs { name, ty, body })) => {
            let var_ty = ast_to_term(*ty, globals, name_stack, infer_dict, infer_cnt)?;
            assert_eq!(name.len(), 1);
            let name = name.into_iter().next().unwrap();
            name_stack.push(name);
            let body = ast_to_term(*body, globals, name_stack, infer_dict, infer_cnt)?;
            let name = name_stack.pop().unwrap();
            let abs = Abstraction {
                var_ty: var_ty.clone(),
                body,
                hint_name: Some(name),
            };
            let fun = pack_abstraction(AbsSign::Fun, abs);
            Ok(app_ref!(set_from_func(), var_ty, fun))
        }
        Set(AstSet::Items(items)) => {
            let w = term_ref!(_ infer_cnt.generate());
            if items.is_empty() {
                return Ok(app_ref!(set_empty(), w));
            }
            let mut items_iter = items.into_iter();
            let exp = items_iter.next().unwrap();
            let term = ast_to_term(exp, globals, name_stack, infer_dict, infer_cnt)?;
            let mut bag = app_ref!(set_singleton(), w, term);

            //push remain element in form {a1} ∪ {a2} ...
            for exp in items_iter {
                let term = ast_to_term(exp, globals, name_stack, infer_dict, infer_cnt)?;
                bag = app_ref!(union(), w, bag, app_ref!(set_singleton(), w, term));
            }
            Ok(bag)
        }
        Abs(sign, AstAbs { name, ty, body }) => {
            let mut ty_term = ast_to_term(*ty, globals, name_stack, infer_dict, infer_cnt)?;
            let mut tys = vec![];
            for n in name {
                tys.push(ty_term.clone());
                ty_term = increase_foreign_vars(ty_term, 0);
                name_stack.push(n);
            }
            let mut r = ast_to_term(*body, globals, name_stack, infer_dict, infer_cnt)?;
            for var_ty in tys.into_iter().rev() {
                let name = name_stack.pop().unwrap();
                let abs = Abstraction {
                    var_ty,
                    body: r,
                    hint_name: Some(name),
                };
                r = pack_abstraction(sign, abs);
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
            ast_to_term(*a, globals, name_stack, infer_dict, infer_cnt)?,
            ast_to_term(*b, globals, name_stack, infer_dict, infer_cnt)?
        )),
        Number(num) => Ok(term_ref!(n num)),
        Wild(n) => {
            let i = match n {
                Some(x) => {
                    if let Some(k) = infer_dict.get(&x) {
                        *k
                    } else {
                        let i = infer_cnt.generate();
                        infer_dict.insert(x, i);
                        i
                    }
                }
                None => infer_cnt.generate(),
            };
            Ok(term_ref!(_ i))
        }
        BinOp(a, op, b) => {
            let ta = ast_to_term(*a, globals, name_stack, infer_dict, infer_cnt)?;
            let tb = ast_to_term(*b, globals, name_stack, infer_dict, infer_cnt)?;
            Ok(op.run_on_term(infer_cnt, ta, tb))
        }
    }
}
