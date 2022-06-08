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
        r.pop_highlight();
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
            AstTerm::UniOp(_, x) => f(x),
            AstTerm::Set(AstSet::Abs(t)) => g(t),
            AstTerm::Set(AstSet::Items(t)) => t.iter_mut().for_each(f),
            AstTerm::Len(x) => f(x),
            AstTerm::Char(_) | AstTerm::Number(_) | AstTerm::Wild(_) | AstTerm::Universe(_) => (),
        }
    }
    f(&mut ast);
    ast
}

#[derive(Debug, Default)]
pub struct HtmlRenderer {
    value: String,
    pos: usize,
}

impl Write for HtmlRenderer {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.pos += s.chars().count();
        self.value.write_str(s)
    }
}

impl AstStacker for HtmlRenderer {
    fn push_highlight(&mut self, highlight: HighlightTag) {
        let pos = self.pos;
        self.value += &format!(r#"<span class="highlight{highlight:?}" data-pos="{pos}">"#);
    }

    fn pop_highlight(&mut self) {
        self.value += "</span>";
    }
}

impl HtmlRenderer {
    pub fn value(self) -> String {
        self.value
    }
}
