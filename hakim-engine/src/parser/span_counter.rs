use std::fmt::Write;

use super::{
    pretty_print::{pretty_print_ast, PrettyPrintConfig},
    semantic_highlight::HighlightTag,
    AstTerm, PrecLevel,
};

#[derive(Debug)]
enum Finder {
    Found(AstTerm),
    Looking {
        l: usize,
        r: usize,
        pos: usize,
        stack: Vec<(usize, AstTerm)>,
    },
}

struct Counter {
    ast: AstTerm,
    pos: usize,
    l: usize,
    r: usize,
    result: usize,
    cnt: usize,
    stack: Vec<Option<usize>>,
}

impl Write for Counter {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.pos += s.chars().count();
        Ok(())
    }
}

impl AstStacker for Counter {
    fn push_highlight(&mut self, _: HighlightTag) {}
    fn pop_highlight(&mut self) {}

    fn push_ast(&mut self, ast: &AstTerm) {
        let is_our = self.ast == *ast;
        if is_our {
            self.cnt += 1;
            self.stack.push(Some(self.pos));
        } else {
            self.stack.push(None)
        }
    }

    fn pop_ast(&mut self) {
        if let Some(x) = self.stack.pop().unwrap() {
            if self.l == x && self.r == self.pos {
                self.result = self.cnt;
            }
        }
    }

    fn paren_open(&mut self) {
        self.stack
            .push(self.stack.last().unwrap().map(|_| self.pos));
    }

    fn paren_close(&mut self) {
        self.pop_ast()
    }
}

impl Write for Finder {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        match self {
            Finder::Found(_) => (),
            Finder::Looking { pos, .. } => {
                *pos += s.chars().count();
            }
        }
        Ok(())
    }
}

pub trait AstStacker: Write {
    fn push_ast(&mut self, _: &AstTerm) {}
    fn pop_ast(&mut self) {}
    fn push_indent(&mut self) {}
    fn pop_indent(&mut self, _: usize) {}
    fn push_highlight(&mut self, _: HighlightTag) {}
    fn pop_highlight(&mut self) {}
    fn paren_open(&mut self) {}
    fn paren_close(&mut self) {}
    fn line_break(&mut self) {
        self.write_str(" ").unwrap()
    }
}

impl AstStacker for Finder {
    fn push_highlight(&mut self, _: HighlightTag) {}
    fn pop_highlight(&mut self) {}

    fn push_ast(&mut self, ast: &AstTerm) {
        match self {
            Finder::Found(_) => (),
            Finder::Looking { pos, stack, .. } => {
                stack.push((*pos, ast.clone()));
            }
        }
    }

    fn pop_ast(&mut self) {
        match self {
            Finder::Found(_) => (),
            Finder::Looking { pos, stack, l, r } => {
                let (posl, x) = stack.pop().unwrap();
                if *l == posl && r == pos {
                    *self = Finder::Found(x);
                }
            }
        }
    }

    fn paren_open(&mut self) {
        match self {
            Finder::Found(_) => (),
            Finder::Looking { stack, .. } => {
                let t = &stack.last().unwrap().1.clone();
                self.push_ast(t);
            }
        }
    }

    fn paren_close(&mut self) {
        self.pop_ast();
    }
}

fn ast_of_span(ast: &AstTerm, span: (usize, usize), c: &PrettyPrintConfig) -> Option<AstTerm> {
    let mut w = Finder::Looking {
        l: span.0,
        r: span.1,
        pos: 0,
        stack: vec![],
    };
    pretty_print_ast(ast, (PrecLevel::MAX, PrecLevel::MAX), &mut w, c).ok()?;
    match w {
        Finder::Found(x) => Some(x),
        Finder::Looking { .. } => None,
    }
}

pub fn pos_of_span(ast: &AstTerm, span: (usize, usize), c: &PrettyPrintConfig) -> Option<usize> {
    let mut w = Counter {
        ast: ast_of_span(ast, span, c)?,
        pos: 0,
        l: span.0,
        r: span.1,
        result: 0,
        cnt: 0,
        stack: vec![],
    };
    pretty_print_ast(ast, (PrecLevel::MAX, PrecLevel::MAX), &mut w, c).ok()?;
    Some(w.result)
}

#[cfg(test)]
mod tests {
    use crate::parser::{
        parse, pretty_print::PrettyPrintConfig, semantic_highlight::fill_highlight_dummy, AstTerm,
    };

    use super::{ast_of_span, pos_of_span};

    fn my_parse(s: &str) -> AstTerm {
        fill_highlight_dummy(parse(s).unwrap())
    }

    fn not_found(s: &str, span: (usize, usize)) {
        let x = my_parse(s);
        assert_eq!(x.to_string(), s);
        let y = ast_of_span(&x, span, &PrettyPrintConfig::default());
        assert!(y.is_none());
    }

    fn one(s: &str, span: (usize, usize), r: &str) {
        let x = my_parse(s);
        assert_eq!(x.to_string(), s);
        let y = ast_of_span(&x, span, &PrettyPrintConfig::default()).unwrap_or_else(|| {
            panic!("bad span {span:?} for {s}");
        });
        assert_eq!(y.to_string(), r);
    }

    fn pos(s: &str, span: (usize, usize), r: usize) {
        let x = my_parse(s);
        assert_eq!(x.to_string(), s);
        let y = pos_of_span(&x, span, &PrettyPrintConfig::default()).unwrap_or_else(|| {
            panic!("bad span {span:?} for {s}");
        });
        assert_eq!(y, r, "failed in {span:?} and {s}");
    }

    #[test]
    fn paren() {
        one("(2 + 3) * 5", (1, 2), "2");
        one("(2 + 3) * 5", (0, 7), "2 + 3");
        one("(2 + 3) * 5", (1, 6), "2 + 3");
        pos("(2 + 3) * (2 + 3) * (2 + 3 + 5)", (1, 6), 1);
        pos("(2 + 3) * (2 + 3) * (2 + 3 + 5)", (0, 7), 1);
        pos("(2 + 3) * (2 + 3) * (2 + 3 + 5)", (10, 17), 2);
        pos("(2 + 3) * (2 + 3) * (2 + 3 + 5)", (11, 16), 2);
        pos("(2 + 3) * (2 + 3) * (2 + 3 + 5)", (21, 26), 3);
    }

    #[test]
    fn simple() {
        one("2 + 3", (0, 1), "2");
        one("2 + 3", (4, 5), "3");
        pos("2 + 2", (0, 1), 1);
        pos("2 + 2", (4, 5), 2);
        one("2 + 3", (0, 5), "2 + 3");
        one("∀ a: ℤ, a * a mod 2 = a mod 2", (22, 29), "a mod 2");
        not_found("∀ a: ℤ, a * a mod 2 = a mod 2", (12, 19));
        pos("∀ a: ℤ, a * a mod 2 = a mod 2", (22, 29), 1);
        pos("∀ a: ℤ, a * (a mod 2) = a mod 2", (24, 31), 2);
        pos("a * a mod 2 = a mod 2", (14, 21), 1);
    }
}
