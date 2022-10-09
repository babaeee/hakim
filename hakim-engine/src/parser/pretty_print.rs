use std::{cmp::min, collections::HashSet, fmt::Display, rc::Rc};

use crate::{
    app_ref,
    brain::{detect_char, detect_len, increase_foreign_vars},
    library::prelude,
    parser::{
        ast::{AstAbs, AstSet, AstSigma},
        tokenizer::AbsSign,
    },
    term_ref, Abstraction, Term, TermRef,
};

use super::{semantic_highlight::HighlightTag, span_counter::AstStacker, AstTerm, PrecLevel};

mod max_width;
pub use max_width::{term_pretty_print_to_html, term_pretty_print_to_string};

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

fn detect_sigma(t: &Term) -> Option<(TermRef, TermRef, TermRef)> {
    if let Term::App { func, op: op2 } = t {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "sigma" {
                        return Some((op.clone(), op1.clone(), op2.clone()));
                    }
                }
            }
        }
    }
    None
}

fn detect_tuple_items(mut t: TermRef) -> Option<Vec<TermRef>> {
    let mut r = vec![];
    loop {
        if let Term::App { func, op: op2 } = t.as_ref() {
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::App { func, op: _ } = func.as_ref() {
                    if let Term::App { func, op: _ } = func.as_ref() {
                        if let Term::Axiom { unique_name, .. } = func.as_ref() {
                            if unique_name == "pair" {
                                r.push(op1.clone());
                                t = op2.clone();
                                continue;
                            }
                        }
                    }
                }
            }
        }
        break;
    }
    if r.is_empty() {
        return None;
    }
    r.push(t);
    Some(r)
}

fn detect_list_items(mut t: &Term) -> Option<(Vec<TermRef>, TermRef)> {
    let mut r = vec![];
    let ty = loop {
        match t {
            Term::App { func, op: op2 } => match func.as_ref() {
                Term::Axiom { unique_name, .. } => {
                    if unique_name == "nil" {
                        break op2.clone();
                    }
                    return None;
                }
                Term::App { func, op: op1 } => match func.as_ref() {
                    Term::App { func, op: _ } => match func.as_ref() {
                        Term::Axiom { unique_name, .. } => {
                            if unique_name == "cons" {
                                t = op2;
                                r.push(op1.clone());
                                continue;
                            }
                            return None;
                        }
                        _ => return None,
                    },
                    _ => return None,
                },
                _ => return None,
            },
            _ => return None,
        }
    };
    Some((r, ty))
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

fn check_name(names: &(Vec<(String, usize, TermRef)>, impl Fn(&str) -> bool), name: &str) -> bool {
    names.1(name) && names.0.iter().all(|x| x.0 != name)
}

fn generate_name(
    names: &(Vec<(String, usize, TermRef)>, impl Fn(&str) -> bool),
    hint: &str,
) -> String {
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
            body: app_ref!(increase_foreign_vars(term), term_ref!(v 0)),
            hint_name: None,
            var_ty: ty,
        }
    }
}

#[cfg(test)]
pub fn structural_print(term: &Term) -> String {
    fn g(w: &mut impl std::fmt::Write, c: char, abs: &Abstraction) -> Result<(), std::fmt::Error> {
        write!(
            w,
            "({c} {}: ",
            abs.hint_name.as_ref().unwrap_or(&"*".to_string())
        )?;
        f(w, &abs.var_ty)?;
        write!(w, ", ")?;
        f(w, &abs.body)?;
        write!(w, ")")
    }
    fn f(w: &mut impl std::fmt::Write, term: &Term) -> Result<(), std::fmt::Error> {
        match term {
            Term::Axiom { unique_name, .. } => write!(w, "{unique_name}"),
            Term::Universe { index } => write!(w, "Universe{index}"),
            Term::Forall(abs) => g(w, '∀', abs),
            Term::Fun(abs) => g(w, 'λ', abs),
            Term::Var { index } => write!(w, "@{index}"),
            Term::Number { value } => write!(w, "{value}"),
            Term::App { func, op } => {
                write!(w, "(")?;
                f(w, func)?;
                write!(w, " ")?;
                f(w, op)?;
                write!(w, ")")
            }
            Term::Wild { index, scope: None } => write!(w, "?{index}"),
            Term::Wild {
                index,
                scope: Some(s),
            } => write!(w, "?{index}{s:?}"),
        }
    }
    let mut s = "".to_string();
    f(&mut s, term).unwrap();
    s
}

pub fn term_to_ast(
    term: &Term,
    names: &mut (Vec<(String, usize, TermRef)>, impl Fn(&str) -> bool),
    c: &PrettyPrintConfig,
) -> AstTerm {
    use super::{binop::BinOp, uniop::UniOp};
    use AstTerm::*;
    fn detect_special(
        term: &Term,
        names: &mut (Vec<(String, usize, TermRef)>, impl Fn(&str) -> bool),
        c: &PrettyPrintConfig,
    ) -> Option<AstTerm> {
        if let Some((_, exp)) = detect_len(term) {
            return Some(Len(Box::new(term_to_ast(&exp, names, c))));
        }
        if let Some(c) = detect_char(term) {
            return Some(Char(c));
        }
        if let Some((ty, fun)) = detect_exists(term) {
            return Some(compress_abs(
                AbsSign::Exists,
                for_abs(&extract_fun_from_term(fun, ty), names, c),
            ));
        }
        if let Some((ty, fun)) = detect_set_fn(term) {
            let x = for_abs(&extract_fun_from_term(fun, ty), names, c);
            return Some(Set(AstSet::Abs(x)));
        }
        if let Some(exp) = detect_set_items(term) {
            return Some(Set(AstSet::Items(
                exp.map(|x| term_to_ast(&x, names, c)).collect(),
            )));
        }
        if let Some(x) = detect_tuple_items(Rc::new(term.clone())) {
            return Some(Tuple(
                x.into_iter().map(|x| term_to_ast(&x, names, c)).collect(),
            ));
        }
        if let Some((l, ty)) = detect_list_items(term) {
            if ty == prelude::char_ty() {
                let as_str = l.iter().map(|x| detect_char(x)).collect::<Option<String>>();
                if let Some(as_str) = as_str {
                    return Some(Str(as_str));
                }
            }
            return Some(List(l.iter().map(|x| term_to_ast(x, names, c)).collect()));
        }
        if let Some((op, t)) = UniOp::detect(term) {
            return Some(UniOp(op, Box::new(term_to_ast(&t, names, c))));
        }
        if let Some((l, r, f)) = detect_sigma(term) {
            let x = for_abs(&extract_fun_from_term(f, prelude::z()), names, c);
            return Some(Sigma(AstSigma {
                l: Box::new(term_to_ast(&l, names, c)),
                r: Box::new(term_to_ast(&r, names, c)),
                var: x.name.into_iter().next().unwrap(),
                body: x.body,
            }));
        }
        if let Some((l, op, r, _)) = BinOp::detect_custom(term, &c.disabled_binops) {
            if op != BinOp::App {
                return Some(BinOp(
                    Box::new(term_to_ast(&l, names, c)),
                    op,
                    Box::new(term_to_ast(&r, names, c)),
                ));
            }
        }
        None
    }
    fn for_abs(
        abs: &Abstraction,
        names: &mut (Vec<(String, usize, TermRef)>, impl Fn(&str) -> bool),
        c: &PrettyPrintConfig,
    ) -> AstAbs {
        let Abstraction {
            var_ty,
            body,
            hint_name,
        } = abs;
        let ty = term_to_ast(var_ty, names, c);
        let name = if let Some(hint) = hint_name {
            generate_name(names, hint)
        } else {
            generate_name(names, "x")
        };
        names.0.push((name.clone(), 0, var_ty.clone()));
        let body = term_to_ast(body, names, c);
        names.0.pop();
        AstAbs {
            name: vec![name],
            tag: Some(HighlightTag::from_type(var_ty)),
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
    if let Some(value) = detect_special(term, names, c) {
        return value;
    }
    let uncurried = app_ref!(increase_foreign_vars(Rc::new(term.clone())), term_ref!(v 0));
    if detect_special(&uncurried, names, c).is_some() {
        let ty = prelude::z(); // FIXME: this is super wrong!!
        let term = term_ref!(fun ty, uncurried);
        return term_to_ast(&term, names, c);
    }
    match term {
        Term::Axiom { unique_name, ty } => {
            Ident(unique_name.clone(), Some(HighlightTag::from_type(ty)))
        }
        Term::Universe { index } => Universe(*index),
        Term::Forall(abs) => compress_abs(AbsSign::Forall, for_abs(abs, names, c)),
        Term::Fun(abs) => compress_abs(AbsSign::Fun, for_abs(abs, names, c)),
        Term::Var { index } => {
            let (var_name, tag) = if let Some(x) = names.0.iter_mut().rev().nth(*index) {
                x.1 += 1;
                (x.0.clone(), HighlightTag::from_type(&x.2))
            } else {
                (format!("@{}", index - names.0.len()), HighlightTag::Ident)
            };
            Ident(var_name, Some(tag))
        }
        Term::Number { value } => Number(value.clone()),
        Term::App { func, op } => {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if let Some(1) = c.names_with_hidden_args.get(unique_name) {
                    return term_to_ast(func, names, c);
                }
            }
            BinOp(
                Box::new(term_to_ast(func, names, c)),
                BinOp::App,
                Box::new(term_to_ast(op, names, c)),
            )
        }
        Term::Wild { index, scope: None } => Wild(Some(format!("{index}"))),
        Term::Wild {
            index,
            scope: Some(s),
        } => Wild(Some(format!(
            "{index}{:?}",
            s.iter()
                .map(|i| if let Some(x) = names.0.iter().rev().nth(*i) {
                    x.0.clone()
                } else {
                    format!("@{}", i - names.0.len())
                })
                .collect::<Vec<_>>()
        ))),
    }
}

impl AstStacker for std::fmt::Formatter<'_> {}

impl AstStacker for String {}

impl Display for AstTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        pretty_print_ast(self, PMX, f, &PrettyPrintConfig::default())
    }
}

const PMX: (PrecLevel, PrecLevel) = (PrecLevel::MAX, PrecLevel::MAX);

#[derive(Default)]
pub struct PrettyPrintConfig {
    pub disabled_binops: HashSet<super::BinOp>,
    pub names_with_hidden_args: im::HashMap<String, usize>,
}

pub fn pretty_print_ast(
    ast: &AstTerm,
    level: (PrecLevel, PrecLevel),
    r: &mut impl AstStacker,
    c: &PrettyPrintConfig,
) -> Result<(), std::fmt::Error> {
    fn with_paren<T: AstStacker>(
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

    fn comma_vec(
        v: &[AstTerm],
        r: &mut impl AstStacker,
        c: &PrettyPrintConfig,
    ) -> Result<(), std::fmt::Error> {
        let mut it = v.iter();
        if let Some(x) = it.next() {
            pretty_print_ast(x, PMX, r, c)?;
            for x in it {
                write!(r, ", ")?;
                pretty_print_ast(x, PMX, r, c)?;
            }
        }
        Ok(())
    }
    use super::binop::BinOp::App;
    r.push_ast(ast);
    match ast {
        AstTerm::Universe(0) => HighlightTag::Type.print(r, |r| write!(r, "Universe"))?,
        AstTerm::Universe(x) => HighlightTag::Type.print(r, |r| write!(r, "Universe{x}"))?,
        AstTerm::Len(x) => {
            let should_paren = level.1 == App.level_right() || level.0 == App.level_right();
            with_paren(should_paren, r, |r| {
                write!(r, "|")?;
                pretty_print_ast(x, PMX, r, c)?;
                write!(r, "|")
            })?;
        }
        AstTerm::Sigma(AstSigma {
            l: left,
            r: right,
            var,
            body,
        }) => {
            let should_paren = level.1 < PrecLevel::MAX || level.0 == App.level_right();
            with_paren(should_paren, r, |r| {
                write!(r, "Σ ")?;
                HighlightTag::Ident.print(r, |r| write!(r, "{var}"))?;
                write!(r, " in [")?;
                pretty_print_ast(left, PMX, r, c)?;
                write!(r, ", ")?;
                pretty_print_ast(right, PMX, r, c)?;
                write!(r, ") ")?;
                pretty_print_ast(body, PMX, r, c)
            })?;
        }
        AstTerm::Abs(
            sign,
            AstAbs {
                name,
                ty,
                body,
                tag,
            },
        ) => {
            let tag = tag.expect("Ast::Abs is not ready for pretty print");
            let should_paren = level.1 < PrecLevel::MAX || level.0 == App.level_right();
            with_paren(should_paren, r, |r| {
                write!(r, "{sign}")?;
                for n in name {
                    tag.print(r, |r| write!(r, " {n}"))?;
                }
                if let Some(ty) = ty {
                    write!(r, ": ")?;
                    pretty_print_ast(ty, level, r, c)?;
                }
                write!(r, ",")?;
                r.push_indent();
                r.line_break();
                pretty_print_ast(body, PMX, r, c)?;
                r.pop_indent(2);
                Ok(())
            })?;
        }
        AstTerm::Ident(name, tag) => tag
            .expect("Ast::Ident is not ready for pretty print")
            .print(r, |r| write!(r, "{name}"))?,
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
                    _ => {
                        r.push_indent();
                        r.line_break();
                        write!(r, "{op} ")?;
                        r.push_indent();
                    }
                }
                pretty_print_ast(b, (op.level_right(), level.1), r, c)?;
                if *op != App {
                    r.pop_indent(2);
                    r.pop_indent(2);
                }
                Ok(())
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
        AstTerm::Char(x) => {
            HighlightTag::String.print(r, |r| write!(r, "'{x}'"))?;
        }
        AstTerm::Str(x) => {
            HighlightTag::String.print(r, |r| write!(r, r#""{x}""#))?;
        }
        AstTerm::Number(x) => {
            HighlightTag::Literal.print(r, |r| write!(r, "{x}"))?;
        }
        AstTerm::Wild(Some(x)) => write!(r, "?{x}")?,
        AstTerm::Wild(None) => write!(r, "?")?,
        AstTerm::Set(AstSet::Abs(AstAbs {
            name,
            ty,
            body,
            tag,
        })) => {
            assert_eq!(name.len(), 1);
            let name = name.iter().next().unwrap();
            write!(r, "{{ ")?;
            tag.expect("Ast::Set is not ready for pretty print")
                .print(r, |r| write!(r, "{name}"))?;
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
            comma_vec(v, r, c)?;
            write!(r, "}}")?;
        }
        AstTerm::List(v) => {
            write!(r, "[")?;
            comma_vec(v, r, c)?;
            write!(r, "]")?;
        }
        AstTerm::Tuple(v) => {
            write!(r, "(")?;
            comma_vec(v, r, c)?;
            write!(r, ")")?;
        }
    }
    r.pop_ast();
    Ok(())
}

pub fn term_pretty_print<T: Default + AstStacker, F: Fn(&str) -> bool>(
    term: &Term,
    contain_name: F,
    c: &PrettyPrintConfig,
) -> T {
    let ast = term_to_ast(term, &mut (vec![], contain_name), c);
    let mut r = T::default();
    if cfg!(test) {
        pretty_print_ast(&ast, PMX, &mut r, c).unwrap();
    } else {
        write!(r, "\u{2068}").unwrap();
        pretty_print_ast(&ast, PMX, &mut r, c).unwrap();
        write!(r, "\u{2069}").unwrap();
    }
    r
}
