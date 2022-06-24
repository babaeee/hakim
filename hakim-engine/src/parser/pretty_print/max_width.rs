use std::fmt::Write;

use pretty::{RcDoc, Render, RenderAnnotated};

use crate::{
    brain::Term,
    parser::{span_counter::AstStacker, HighlightTag, HtmlRenderer},
};

use super::{term_pretty_print, PrettyPrintConfig};

struct MyRcDoc<'a>(Vec<RcDoc<'a, HighlightTag>>);

impl Default for MyRcDoc<'_> {
    fn default() -> Self {
        Self(vec![RcDoc::text("")])
    }
}

impl Write for MyRcDoc<'_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        let x = self.0.last_mut().unwrap();
        *x = x.clone().append(RcDoc::text(s.to_string()));
        Ok(())
    }
}

impl AstStacker for MyRcDoc<'_> {
    fn line_break(&mut self) {
        let x = self.0.last_mut().unwrap();
        *x = x.clone().append(RcDoc::line());
    }

    fn push_highlight(&mut self, _: HighlightTag) {
        self.0.push(RcDoc::text(""));
    }

    fn pop_highlight(&mut self, ht: HighlightTag) {
        let l = self.0.pop().unwrap();
        let x = self.0.last_mut().unwrap();
        *x = x.clone().append(RcDoc::annotate(l, ht));
    }

    fn push_ast(&mut self, _: &crate::parser::AstTerm) {
        self.0.push(RcDoc::text(""));
    }

    fn pop_ast(&mut self) {
        let l = self.0.pop().unwrap();
        let x = self.0.last_mut().unwrap();
        *x = x.clone().append(RcDoc::group(l));
    }

    fn push_indent(&mut self) {
        self.0.push(RcDoc::text(""));
    }

    fn pop_indent(&mut self, t: usize) {
        let l = self.0.pop().unwrap().nest(t as isize);
        let x = self.0.last_mut().unwrap();
        *x = x.clone().append(l);
    }
}

pub fn term_pretty_print_to_string<F: Fn(&str) -> bool>(
    term: &Term,
    contain_name: F,
    c: &PrettyPrintConfig,
) -> String {
    let x: MyRcDoc = term_pretty_print(term, contain_name, c);
    let mut w = Vec::new();
    assert_eq!(x.0.len(), 1);
    x.0.last().unwrap().render(80, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

struct MyHtmlRenderer(HtmlRenderer);

impl Render for MyHtmlRenderer {
    type Error = ();

    fn write_str(&mut self, s: &str) -> Result<usize, Self::Error> {
        self.0.write_str(s).unwrap();
        Ok(s.len())
    }

    fn fail_doc(&self) -> Self::Error {
        todo!()
    }
}

impl<'a> RenderAnnotated<'a, HighlightTag> for MyHtmlRenderer {
    fn push_annotation(&mut self, annotation: &'a HighlightTag) -> Result<(), Self::Error> {
        self.0.push_highlight(*annotation);
        Ok(())
    }

    fn pop_annotation(&mut self) -> Result<(), Self::Error> {
        self.0.pop_highlight(HighlightTag::Ident);
        Ok(())
    }
}

pub fn term_pretty_print_to_html<F: Fn(&str) -> bool>(
    term: &Term,
    contain_name: F,
    c: &PrettyPrintConfig,
) -> String {
    let x: MyRcDoc = term_pretty_print(term, contain_name, c);
    let mut w = MyHtmlRenderer(HtmlRenderer::default());
    assert_eq!(x.0.len(), 1);
    x.0.last().unwrap().render_raw(80, &mut w).unwrap();
    w.0.value()
}
