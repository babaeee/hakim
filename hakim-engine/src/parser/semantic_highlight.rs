use std::fmt::Write;

use crate::brain::Term;

use super::span_counter::AstStacker;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum HighlightTag {
    Literal,
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

#[derive(Debug, Default)]
pub struct HtmlRenderer(String);

impl Write for HtmlRenderer {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.write_str(s)
    }
}

impl AstStacker for HtmlRenderer {
    fn push_highlight(&mut self, highlight: HighlightTag) {
        self.0 += &format!(r#"<span class="highlight{highlight:?}">"#);
    }

    fn pop_highlight(&mut self) {
        self.0 += "</span>";
    }
}

impl HtmlRenderer {
    pub fn value(self) -> String {
        self.0
    }
}
