use std::{
    cmp::min,
    collections::HashSet,
    fmt::{Display, Write},
};

use crate::{
    app_ref,
    parser::{
        ast::{AstAbs, AstSet},
        tokenizer::AbsSign,
    },
    term_ref, Abstraction, Term, TermRef,
};

use super::{span_counter::AstStacker, AstTerm, PrecLevel};

fn detect_set_singleton(t: &Term) -> Option<TermRef> {
    if let Term::App { func, op: op2 } = t {
        if let Term::App { func, op: _ } = func.as_ref() {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "set_singleton" {
                    return Some(op2.clone());
                }
            }
        }
    }
    None
}

fn detect_set_items(mut t: &Term) -> Option<impl Iterator<Item = TermRef>> {
    let mut r = vec![];
    loop {
        if let Some(item) = detect_set_singleton(t) {
            r.push(item);
            break;
        }
        match t {
            Term::App { func, op: op2 } => match func.as_ref() {
                Term::App { func, op: op1 } => match func.as_ref() {
                    Term::App { func, op: _ } => match func.as_ref() {
                        Term::Axiom { ty: _, unique_name } => {
                            if unique_name == "union" {
                                if let Some(item) = detect_set_singleton(op2) {
                                    r.push(item);
                                    t = op1;
                                    continue;
                                }
                            }
                            return None;
                        }
                        _ => return None,
                    },
                    _ => return None,
                },
                Term::Axiom { ty: _, unique_name } => {
                    if unique_name == "set_empty" {
                        break;
                    } else {
                        return None;
                    }
                }
                _ => return None,
            },
            _ => return None,
        }
    }
    Some(r.into_iter().rev())
}

fn detect_set_fn(t: &Term) -> Option<(TermRef, TermRef)> {
    match t {
        Term::App { func, op: op2 } => match func.as_ref() {
            Term::App { func, op: op1 } => match func.as_ref() {
                Term::Axiom { ty: _, unique_name } => {
                    if unique_name == "set_from_func" {
                        Some((op1.clone(), op2.clone()))
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn detect_len(t: &Term) -> Option<(TermRef, TermRef)> {
    match t {
        Term::App { func, op: op2 } => match func.as_ref() {
            Term::App { func, op: op1 } => match func.as_ref() {
                Term::Axiom { ty: _, unique_name } => {
                    if unique_name == "len1" {
                        Some((op1.clone(), op2.clone()))
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn detect_exists(t: &Term) -> Option<(TermRef, TermRef)> {
    match t {
        Term::App { func, op: op2 } => match func.as_ref() {
            Term::App { func, op: op1 } => match func.as_ref() {
                Term::Axiom { ty: _, unique_name } => {
                    if unique_name == "ex" {
                        Some((op1.clone(), op2.clone()))
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn check_name(names: &(Vec<(String, usize)>, impl Fn(&str) -> bool), name: &str) -> bool {
    names.1(name) && names.0.iter().all(|x| x.0 != name)
}

fn generate_name(names: &(Vec<(String, usize)>, impl Fn(&str) -> bool), hint: &str) -> String {
    if check_name(names, hint) {
        return hint.to_string();
    }
    for i in 0.. {
        let hint = format!("{}{}", hint, i);
        if check_name(names, &hint) {
            return hint;
        }
    }
    unreachable!();
}

fn extract_fun_from_term(term: TermRef, ty: TermRef) -> Abstraction {
    if let Term::Fun(abs) = term.as_ref() {
        abs.clone()
    } else {
        Abstraction {
            body: app_ref!(term, term_ref!(v 0)),
            hint_name: None,
            var_ty: ty,
        }
    }
}

pub fn term_to_ast(
    term: &Term,
    names: &mut (Vec<(String, usize)>, impl Fn(&str) -> bool),
    c: &PrettyPrintConfig,
) -> AstTerm {
    use super::{binop::BinOp, uniop::UniOp};
    use AstTerm::*;
    fn for_abs(
        abs: &Abstraction,
        names: &mut (Vec<(String, usize)>, impl Fn(&str) -> bool),
        c: &PrettyPrintConfig,
    ) -> AstAbs {
        let Abstraction {
            var_ty,
            body,
            hint_name,
        } = abs;
        let name = if let Some(hint) = hint_name {
            generate_name(names, hint)
        } else {
            generate_name(names, "x")
        };
        let ty = term_to_ast(var_ty, names, c);
        names.0.push((name.clone(), 0));
        let body = term_to_ast(body, names, c);
        names.0.pop();
        AstAbs {
            name: vec![name],
            ty: Some(Box::new(ty)),
            body: Box::new(body),
        }
    }
    fn compress_abs(sign: AbsSign, body: AstAbs) -> AstTerm {
        match *body.body {
            Abs(s, mut child) if s == sign && child.ty == body.ty => {
                child.name = [body.name, child.name].concat();
                Abs(sign, child)
            }
            _ => Abs(sign, body),
        }
    }
    if let Some((_, exp)) = detect_len(term) {
        return Len(Box::new(term_to_ast(&exp, names, c)));
    }
    if let Some((ty, fun)) = detect_exists(term) {
        return compress_abs(
            AbsSign::Exists,
            for_abs(&extract_fun_from_term(fun, ty), names, c),
        );
    }
    if let Some((ty, fun)) = detect_set_fn(term) {
        let x = for_abs(&extract_fun_from_term(fun, ty), names, c);
        return Set(AstSet::Abs(x));
    }
    if let Some(exp) = detect_set_items(term) {
        return Set(AstSet::Items(
            exp.map(|x| term_to_ast(&x, names, c)).collect(),
        ));
    }
    if let Some((op, t)) = UniOp::detect(term) {
        return UniOp(op, Box::new(term_to_ast(&t, names, c)));
    }
    if let Some((l, op, r)) = BinOp::detect(term) {
        if !c.disabled_binops.contains(&op) {
            return BinOp(
                Box::new(term_to_ast(&l, names, c)),
                op,
                Box::new(term_to_ast(&r, names, c)),
            );
        }
    }
    match term {
        Term::Axiom { unique_name, .. } => Ident(unique_name.clone()),
        Term::Universe { index } => Universe(*index),
        Term::Forall(abs) => compress_abs(AbsSign::Forall, for_abs(abs, names, c)),
        Term::Fun(abs) => compress_abs(AbsSign::Fun, for_abs(abs, names, c)),
        Term::Var { index } => Ident(if let Some(x) = names.0.iter_mut().rev().nth(*index) {
            x.1 += 1;
            x.0.clone()
        } else {
            format!("@{}", index - names.0.len())
        }),
        Term::Number { value } => Number(value.clone()),
        Term::App { func, op } => BinOp(
            Box::new(term_to_ast(func, names, c)),
            BinOp::App,
            Box::new(term_to_ast(op, names, c)),
        ),
        Term::Wild { index, .. } => Wild(Some(format!("{index}"))),
    }
}

impl AstStacker for std::fmt::Formatter<'_> {
    fn push_ast(&mut self, _: &AstTerm) {}
    fn pop_ast(&mut self) {}
    fn paren_open(&mut self) {}
    fn paren_close(&mut self) {}
}

impl AstStacker for String {
    fn push_ast(&mut self, _: &AstTerm) {}
    fn pop_ast(&mut self) {}
    fn paren_open(&mut self) {}
    fn paren_close(&mut self) {}
}

impl Display for AstTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        pretty_print_ast(self, PMX, f, &PrettyPrintConfig::default())
    }
}

const PMX: (PrecLevel, PrecLevel) = (PrecLevel::MAX, PrecLevel::MAX);

#[derive(Default)]
pub struct PrettyPrintConfig {
    pub disabled_binops: HashSet<super::BinOp>,
}

pub fn pretty_print_ast(
    ast: &AstTerm,
    level: (PrecLevel, PrecLevel),
    r: &mut (impl Write + AstStacker),
    c: &PrettyPrintConfig,
) -> Result<(), std::fmt::Error> {
    fn with_paren<T: Write + AstStacker>(
        should_paren: bool,
        r: &mut T,
        f: impl FnOnce(&mut T) -> Result<(), std::fmt::Error>,
    ) -> Result<(), std::fmt::Error> {
        if should_paren {
            write!(r, "(")?;
        }
        r.paren_open();
        f(r)?;
        r.paren_close();
        if should_paren {
            write!(r, ")")?;
        }
        Ok(())
    }
    use super::binop::BinOp::App;
    r.push_ast(ast);
    match ast {
        AstTerm::Universe(0) => write!(r, "Universe")?,
        AstTerm::Universe(x) => write!(r, "Universe{x}")?,
        AstTerm::Len(x) => {
            let should_paren = level.1 == App.level_right() || level.0 == App.level_right();
            with_paren(should_paren, r, |r| {
                write!(r, "|")?;
                pretty_print_ast(x, PMX, r, c)?;
                write!(r, "|")
            })?;
        }
        AstTerm::Abs(sign, AstAbs { name, ty, body }) => {
            let should_paren = level.1 < PrecLevel::MAX || level.0 == App.level_right();
            with_paren(should_paren, r, |r| {
                write!(r, "{sign}")?;
                for n in name {
                    write!(r, " {n}")?;
                }
                if let Some(ty) = ty {
                    write!(r, ": ")?;
                    pretty_print_ast(ty, level, r, c)?;
                }
                write!(r, ", ")?;
                pretty_print_ast(body, PMX, r, c)
            })?;
        }
        AstTerm::Ident(x) => write!(r, "{x}")?,
        AstTerm::BinOp(a, op, b) => {
            let (level, should_paren) = if min(level.0, level.1) < op.prec() {
                ((PrecLevel::MAX, PrecLevel::MAX), true)
            } else {
                (level, false)
            };
            with_paren(should_paren, r, |r| {
                pretty_print_ast(a, (level.0, op.level_left()), r, c)?;
                match op {
                    App => write!(r, " ")?,
                    _ => write!(r, " {op} ")?,
                }
                pretty_print_ast(b, (op.level_right(), level.1), r, c)
            })?;
        }
        AstTerm::UniOp(op, t) => {
            let should_paren = level.1 < op.prec() || level.0 == App.level_right();
            with_paren(should_paren, r, |r| {
                write!(r, "{op} ")?;
                let level_r = if should_paren {
                    PrecLevel::MAX
                } else {
                    level.1
                };
                pretty_print_ast(t, (op.prec(), level_r), r, c)
            })?;
        }
        AstTerm::Number(x) => write!(r, "{x}")?,
        AstTerm::Wild(Some(x)) => write!(r, "?{x}")?,
        AstTerm::Wild(None) => write!(r, "?")?,
        AstTerm::Set(AstSet::Abs(AstAbs { name, ty, body })) => {
            assert_eq!(name.len(), 1);
            let name = name.iter().next().unwrap();
            write!(r, "{{ {name}")?;
            if let Some(ty) = ty {
                write!(r, ": ")?;
                pretty_print_ast(ty, PMX, r, c)?;
            }
            write!(r, " | ")?;
            pretty_print_ast(body, PMX, r, c)?;
            write!(r, " }}")?;
        }
        AstTerm::Set(AstSet::Items(v)) => {
            write!(r, "{{")?;
            let mut it = v.iter();
            if let Some(x) = it.next() {
                pretty_print_ast(x, PMX, r, c)?;
                for x in it {
                    write!(r, ", ")?;
                    pretty_print_ast(x, PMX, r, c)?;
                }
            }
            write!(r, "}}")?;
        }
    }
    r.pop_ast();
    Ok(())
}

pub fn term_pretty_print(
    term: &Term,
    contain_name: impl Fn(&str) -> bool,
    c: &PrettyPrintConfig,
) -> String {
    let ast = term_to_ast(term, &mut (vec![], contain_name), c);
    let mut r = String::new();
    if cfg!(test) {
        pretty_print_ast(&ast, PMX, &mut r, c).unwrap();
    } else {
        r.push('\u{2068}');
        pretty_print_ast(&ast, PMX, &mut r, c).unwrap();
        r.push('\u{2069}');
    }
    r
}
