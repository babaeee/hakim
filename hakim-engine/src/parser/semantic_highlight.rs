use std::fmt::Write;

use crate::brain::Term;

use super::span_counter::AstStacker;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum HighlightTag {
    Literal,
    String,
    Type,
    Function,
    Ident,
}

impl HighlightTag {
    pub fn from_type(ty: &Term) -> Self {
        match ty {
            Term::Universe { .. } => Self::Type,
            Term::Forall(_) => Self::Function,
            _ => Self::Ident,
        }
    }

    pub fn print<T: AstStacker>(
        &self,
        r: &mut T,
        f: impl FnOnce(&mut T) -> Result<(), std::fmt::Error>,
    ) -> Result<(), std::fmt::Error> {
        r.push_highlight(*self);
        f(r)?;
        r.pop_highlight(*self);
        Ok(())
    }
}

#[cfg(test)]
use super::{
    ast::{AstAbs, AstSet},
    AstTerm,
};

#[cfg(test)]
pub fn fill_highlight_dummy(mut ast: AstTerm) -> AstTerm {
    use crate::parser::ast::AstSigma;

    fn e(a: &mut Option<HighlightTag>) {
        if a.is_none() {
            *a = Some(HighlightTag::Ident)
        }
    }
    fn g(a: &mut AstAbs) {
        let AstAbs { tag, ty, body, .. } = a;
        e(tag);
        ty.iter_mut().for_each(|x| f(x));
        f(body);
    }
    fn f(a: &mut AstTerm) {
        match a {
            AstTerm::Abs(_, t) => g(t),
            AstTerm::Ident(_, s) => e(s),
            AstTerm::BinOp(x, _, y) => {
                f(x);
                f(y);
            }
            AstTerm::Sigma(AstSigma { l, r, var: _, body }) => {
                f(l);
                f(r);
                f(body);
            }
            AstTerm::UniOp(_, x) => f(x),
            AstTerm::Set(AstSet::Abs(t)) => g(t),
            AstTerm::Set(AstSet::Items(t)) => t.iter_mut().for_each(f),
            AstTerm::Tuple(t) | AstTerm::List(t) => t.iter_mut().for_each(f),
            AstTerm::Len(x) => f(x),
            AstTerm::Char(_)
            | AstTerm::Str(_)
            | AstTerm::Number(_)
            | AstTerm::Wild(_)
            | AstTerm::Universe(_) => (),
        }
    }
    f(&mut ast);
    ast
}

#[derive(Debug)]
pub struct HtmlRenderer {
    value: String,
    pos: usize,
    ignored: bool,
}

impl Default for HtmlRenderer {
    fn default() -> Self {
        Self {
            value: Default::default(),
            pos: 0,
            ignored: true,
        }
    }
}

impl Write for HtmlRenderer {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        for c in s.chars() {
            if c == '\n' {
                self.pos += 1;
                self.ignored = true;
                self.value.push(c);
                continue;
            }
            if self.ignored {
                if c == ' ' {
                    self.value.push(c);
                    continue;
                }
                self.ignored = false;
            }
            write!(self.value, r#"<span data-pos="{}">"#, self.pos).unwrap();
            self.pos += 1;
            self.value.push(c);
            self.value += "</span>";
        }
        Ok(())
    }
}

impl AstStacker for HtmlRenderer {
    fn push_highlight(&mut self, highlight: HighlightTag) {
        let pos = self.pos;
        write!(
            self.value,
            r#"<span class="highlight{highlight:?}" data-pos="{pos}">"#
        )
        .unwrap();
    }

    fn pop_highlight(&mut self, _: HighlightTag) {
        self.value += "</span>";
    }
}

impl HtmlRenderer {
    pub fn value(self) -> String {
        self.value
    }
}
