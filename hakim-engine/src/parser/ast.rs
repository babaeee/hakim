use std::collections::HashMap;

use super::{
    tokenizer::{AbsSign, Token, TokenValue},
    uniop::UniOp,
    wild::InferGenerator,
    Error::*,
    HighlightTag, ParserConfig, Result,
};

use crate::{
    app_ref,
    brain::{good_char, increase_foreign_vars, Abstraction, Term, TermRef},
    library::prelude::{
        self, chr, ex, len1, pair, set_empty, set_from_func, set_singleton, sigma, union,
    },
    parser::binop::{Assoc, BinOp},
    term_ref,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AstAbs {
    pub name: Vec<String>,
    pub tag: Option<HighlightTag>,
    pub ty: Option<Box<AstTerm>>,
    pub body: Box<AstTerm>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstSet {
    Abs(AstAbs),
    Items(Vec<AstTerm>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AstSigma {
    pub l: Box<AstTerm>,
    pub r: Box<AstTerm>,
    pub var: String,
    pub body: Box<AstTerm>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstTerm {
    Universe(usize),
    Abs(AbsSign, AstAbs),
    Ident(String, Option<HighlightTag>),
    BinOp(Box<AstTerm>, BinOp, Box<AstTerm>),
    UniOp(UniOp, Box<AstTerm>),
    Number(BigInt),
    Char(char),
    Str(String),
    List(Vec<AstTerm>),
    Tuple(Vec<AstTerm>),
    Wild(Option<String>),
    Len(Box<AstTerm>),
    Set(AstSet),
    Sigma(AstSigma),
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
        if let TokenValue::Ident(s) = t.value {
            self.eat_token()?;
            Ok(s)
        } else {
            Err(ExpectedIdentButGot(t.clone()))
        }
    }

    fn eat_ident_vec(&mut self) -> Result<Vec<String>> {
        let mut v = vec![];
        while let TokenValue::Ident(s) = self.peek_token()?.value {
            self.eat_token()?;
            v.push(s);
        }
        Ok(v)
    }

    fn eat_sign(&mut self, sign: &str) -> Result<()> {
        let t = self.peek_token()?;
        if let TokenValue::Sign(s) = t.value {
            if s == sign {
                self.eat_token()?;
                Ok(())
            } else {
                Err(ExpectedSignButGot(
                    sign.to_string(),
                    Token {
                        value: TokenValue::Sign(s),
                        ..t
                    },
                ))
            }
        } else {
            Err(ExpectedSignButGot(sign.to_string(), t.clone()))
        }
    }

    fn eat_comma_vec(&mut self, terminator: &TokenValue) -> Result<Vec<AstTerm>> {
        let mut r = vec![];
        loop {
            if self.peek_token()?.value == *terminator {
                self.eat_token()?;
                return Ok(r);
            }
            r.push(self.eat_ast()?);
            if self.peek_token()?.value == *terminator {
                self.eat_token()?;
                break Ok(r);
            }
            self.eat_sign(",")?;
        }
    }

    fn eat_set(&mut self) -> Result<AstTerm> {
        // we already eated Sign("{")
        if self.look_ahead(1).map(|x| x.value) == Ok(TokenValue::Sign(":".to_string())) {
            let name = vec![self.eat_ident()?];
            self.eat_sign(":")?;
            let ty = Some(Box::new(self.eat_ast_with_disallowed_sign(|x| x == "|")?));
            self.eat_sign("|")?;
            let body = Box::new(self.eat_ast()?);
            self.eat_sign("}")?;
            Ok(Set(AstSet::Abs(AstAbs {
                name,
                ty,
                body,
                tag: None,
            })))
        } else if self.look_ahead(1).map(|x| x.value) == Ok(TokenValue::Sign("|".to_string())) {
            let name = vec![self.eat_ident()?];
            self.eat_sign("|")?;
            let body = Box::new(self.eat_ast()?);
            self.eat_sign("}")?;
            Ok(Set(AstSet::Abs(AstAbs {
                name,
                ty: None,
                body,
                tag: None,
            })))
        } else {
            Ok(Set(AstSet::Items(
                self.eat_comma_vec(&TokenValue::Sign("}".to_string()))?,
            )))
        }
    }

    fn eat_ast_without_app(&mut self) -> Result<AstTerm> {
        let t = self.eat_token()?;
        match t.value {
            TokenValue::Ident(s) => {
                if let Some(index) = s.strip_prefix("Universe") {
                    if index.is_empty() {
                        Ok(Universe(0))
                    } else {
                        let parsed: std::result::Result<usize, _> = index.parse();
                        match parsed {
                            Ok(x) if x < 1000 => Ok(Universe(x)),
                            _ => Err(InvalidUniverseIndex(s)),
                        }
                    }
                } else {
                    Ok(Ident(s, None))
                }
            }
            TokenValue::Wild(i) => {
                let t = Wild(i);
                Ok(t)
            }
            TokenValue::Abs(sign) => {
                let name = self.eat_ident_vec()?;
                let ty = if self.peek_token()?.value == TokenValue::Sign(",".to_string()) {
                    None
                } else {
                    self.eat_sign(":")?;
                    Some(Box::new(self.eat_ast()?))
                };
                self.eat_sign(",")?;
                let body = Box::new(self.eat_ast()?);
                Ok(Abs(
                    sign,
                    AstAbs {
                        name,
                        ty,
                        body,
                        tag: None,
                    },
                ))
            }
            TokenValue::Sign(s) => match s.as_str() {
                "(" => {
                    let r = self.eat_comma_vec(&TokenValue::Sign(")".to_string()))?;
                    match r.len() {
                        0 => Err(InvalidUnitTuple),
                        1 => Ok(r.into_iter().next().unwrap()),
                        _ => Ok(Tuple(r)),
                    }
                }
                "[" => {
                    let r = self.eat_comma_vec(&TokenValue::Sign("]".to_string()))?;
                    Ok(List(r))
                }
                "{" => self.eat_set(),
                "|" => {
                    let r = self.eat_ast_with_disallowed_sign(|x| x == "|")?;
                    self.eat_sign("|")?;
                    Ok(Len(Box::new(r)))
                }
                "Σ" => {
                    let var = self.eat_ident()?;
                    self.eat_sign("in")?;
                    self.eat_sign("[")?;
                    let [l, r] =
                        <[_; 2]>::try_from(self.eat_comma_vec(&TokenValue::Sign(")".to_string()))?)
                            .map_err(|_| BadSigma)?
                            .map(Box::new);
                    let body = Box::new(self.eat_ast()?);
                    Ok(Sigma(AstSigma { l, r, var, body }))
                }
                _ => Err(ExpectedExprButGot(Token {
                    value: TokenValue::Sign(s),
                    ..t
                })),
            },
            TokenValue::Number(x) => Ok(Number(x)),
            TokenValue::Char(c) => Ok(Char(c)),
            TokenValue::Str(c) => Ok(Str(c)),
        }
    }

    fn eat_ast(&mut self) -> Result<AstTerm> {
        self.eat_ast_with_disallowed_sign(|_| false)
    }

    fn eat_ast_with_disallowed_sign(&mut self, disallow_sign: fn(&str) -> bool) -> Result<AstTerm> {
        enum Op {
            Bin(AstTerm, BinOp),
            Uni(UniOp),
        }
        use Op::*;
        fn push_to_stack(stack: &mut Vec<Op>, op: BinOp, mut n: AstTerm) {
            while let Some(x) = stack.last() {
                match x {
                    Bin(_, op2) => {
                        if op2.prec() > op.prec() {
                            break;
                        }
                        if op2.prec() == op.prec() && op.assoc() == Assoc::Right {
                            break;
                        }
                    }
                    Uni(x) => {
                        if x.prec() > op.prec() {
                            break;
                        }
                    }
                }
                match stack.pop().unwrap() {
                    Bin(n2, op2) => {
                        n = BinOp(Box::new(n2), op2, Box::new(n));
                    }
                    Uni(op2) => {
                        n = UniOp(op2, Box::new(n));
                    }
                };
            }
            stack.push(Bin(n, op));
        }
        let mut cur_opt = None;
        let mut stack: Vec<Op> = vec![];
        loop {
            let cur = if let Some(c) = cur_opt {
                c
            } else {
                if let Ok(TokenValue::Sign(s)) = self.peek_token().map(|x| x.value) {
                    if let Some(op) = UniOp::from_str(&s) {
                        self.eat_token()?;
                        stack.push(Uni(op));
                        continue;
                    }
                }
                cur_opt = Some(self.eat_ast_without_app()?);
                continue;
            };
            let t = match self.peek_token() {
                Ok(k) => k,
                Err(UnexpectedEOF) => {
                    cur_opt = Some(cur);
                    break;
                }
                Err(err) => return Err(err),
            };
            if let TokenValue::Sign(s) = t.value {
                if disallow_sign(&s) {
                    cur_opt = Some(cur);
                    break;
                }
                if let Some(op) = BinOp::from_str(&s) {
                    self.eat_token()?;
                    push_to_stack(&mut stack, op, cur);
                    cur_opt = None;
                    continue;
                }
                if s == "(" || s == "{" || s == "[" {
                    push_to_stack(&mut stack, BinOp::App, cur);
                    cur_opt = None;
                    continue;
                }
                cur_opt = Some(cur);
                break;
            }
            push_to_stack(&mut stack, BinOp::App, cur);
            cur_opt = None;
        }
        let mut cur = cur_opt.unwrap();
        for x in stack.into_iter().rev() {
            match x {
                Bin(t, op) => {
                    cur = BinOp(Box::new(t), op, Box::new(cur));
                }
                Uni(op) => {
                    cur = UniOp(op, Box::new(cur));
                }
            }
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
    config: &ParserConfig,
) -> Result<TermRef> {
    match ast {
        Universe(x) => Ok(term_ref!(universe x)),
        Set(AstSet::Abs(AstAbs { name, ty, body, .. })) => {
            let var_ty = match ty {
                Some(ty) => ast_to_term(*ty, globals, name_stack, infer_dict, infer_cnt, config)?,
                None => term_ref!(_ infer_cnt.generate()),
            };
            assert_eq!(name.len(), 1);
            let name = name.into_iter().next().unwrap();
            name_stack.push(name);
            let body = ast_to_term(*body, globals, name_stack, infer_dict, infer_cnt, config)?;
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
            let term = ast_to_term(exp, globals, name_stack, infer_dict, infer_cnt, config)?;
            let mut bag = app_ref!(set_singleton(), w, term);

            //push remain element in form {a1} ∪ {a2} ...
            for exp in items_iter {
                let term = ast_to_term(exp, globals, name_stack, infer_dict, infer_cnt, config)?;
                bag = app_ref!(union(), w, bag, app_ref!(set_singleton(), w, term));
            }
            Ok(bag)
        }
        Sigma(AstSigma { l, r, var, body }) => {
            let l = ast_to_term(*l, globals, name_stack, infer_dict, infer_cnt, config)?;
            let r = ast_to_term(*r, globals, name_stack, infer_dict, infer_cnt, config)?;
            let f = ast_to_term(
                AstTerm::Abs(
                    AbsSign::Fun,
                    AstAbs {
                        name: vec![var],
                        tag: None,
                        ty: Some(Box::new(Ident("ℤ".to_string(), None))),
                        body,
                    },
                ),
                globals,
                name_stack,
                infer_dict,
                infer_cnt,
                config,
            )?;
            Ok(app_ref!(sigma(), l, r, f))
        }
        Abs(sign, AstAbs { name, ty, body, .. }) => {
            let mut ty_term = match ty {
                Some(ty) => ast_to_term(*ty, globals, name_stack, infer_dict, infer_cnt, config)?,
                None => term_ref!(_ infer_cnt.generate()),
            };
            let mut tys = vec![];
            for n in name {
                tys.push(ty_term.clone());
                ty_term = increase_foreign_vars(ty_term, 0);
                name_stack.push(n);
            }
            let mut r = ast_to_term(*body, globals, name_stack, infer_dict, infer_cnt, config)?;
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
        Ident(s, _) => {
            if let Some(i) = name_stack.iter().rev().position(|x| *x == s) {
                return Ok(term_ref!(v i));
            }
            if let Some(t) = globals.get(&s) {
                let tvars = config.names_with_hidden_args.get(&s).copied().unwrap_or(0);
                let mut r = t.clone();
                for _ in 0..tvars {
                    let vn = infer_cnt.generate();
                    let v = term_ref!(_ vn);
                    r = app_ref!(r, v);
                }
                Ok(r)
            } else {
                Err(UndefinedName(s))
            }
        }
        Number(num) => Ok(term_ref!(n num)),
        Str(s) => {
            let v = s.chars().map(char_to_term).collect::<Result<Vec<_>>>()?;
            let r = list_to_term(v, prelude::char_ty());
            Ok(r)
        }
        List(v) => {
            let v = v
                .into_iter()
                .map(|x| ast_to_term(x, globals, name_stack, infer_dict, infer_cnt, config))
                .collect::<Result<Vec<_>>>()?;
            let ty = term_ref!(_ infer_cnt.generate());
            let r = list_to_term(v, ty);
            Ok(r)
        }
        Tuple(v) => {
            let v = v
                .into_iter()
                .map(|x| ast_to_term(x, globals, name_stack, infer_dict, infer_cnt, config))
                .collect::<Result<Vec<_>>>()?;
            let mut make_pair = |a: TermRef, b: TermRef| -> TermRef {
                let ta = term_ref!(_ infer_cnt.generate());
                let tb = term_ref!(_ infer_cnt.generate());
                app_ref!(app_ref!(pair(), ta), tb, a, b)
            };
            let r = {
                let mut v = v.into_iter().rev();
                let a = v.next().unwrap();
                let b = v.next().unwrap();
                let mut result = make_pair(b, a);
                for x in v.into_iter().rev() {
                    result = make_pair(x, result);
                }
                result
            };
            Ok(r)
        }
        Char(c) => char_to_term(c),
        Len(a) => {
            let ta = ast_to_term(*a, globals, name_stack, infer_dict, infer_cnt, config)?;
            let vn = infer_cnt.generate();
            let v = term_ref!(_ vn);
            Ok(app_ref!(len1(), v, ta))
        }
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
        UniOp(op, a) => {
            let ta = ast_to_term(*a, globals, name_stack, infer_dict, infer_cnt, config)?;
            Ok(op.run_on_term(infer_cnt, ta))
        }
        BinOp(a, op, b) => {
            let ta = ast_to_term(*a, globals, name_stack, infer_dict, infer_cnt, config)?;
            let tb = ast_to_term(*b, globals, name_stack, infer_dict, infer_cnt, config)?;
            Ok(op.run_on_term(infer_cnt, ta, tb))
        }
    }
}

fn list_to_term(it: Vec<TermRef>, ty: TermRef) -> TermRef {
    let mut result = app_ref!(prelude::nil(), ty);
    for x in it.into_iter().rev() {
        result = app_ref!(prelude::cons(), ty, x, result);
    }
    result
}

fn char_to_term(c: char) -> Result<TermRef> {
    if !good_char(c) {
        return Err(BadChar(c));
    }
    let num = BigInt::from(u32::from(c));
    let nt = term_ref!(n num);
    Ok(app_ref!(chr(), nt))
}
