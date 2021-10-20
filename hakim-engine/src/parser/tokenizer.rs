#[derive(Debug, Clone, PartialEq)]
pub enum Keyword {
    Forall,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Ident(String),
    Kw(Keyword),
    Sign(String),
    Number(u32),
    Wild(usize),
}

use Keyword::*;
use Token::*;

trait Eater {
    fn pick_char(&self) -> Option<char>;
    fn eat_char(&mut self) -> char;
    fn eat_prefix(&mut self, prefix: &str) -> bool;
}

impl Eater for &str {
    fn pick_char(&self) -> Option<char> {
        self.chars().next()
    }

    fn eat_char(&mut self) -> char {
        let c = self.chars().next().unwrap();
        *self = &self[c.len_utf8()..];
        c
    }

    fn eat_prefix(&mut self, prefix: &str) -> bool {
        if let Some(k) = self.strip_prefix(prefix) {
            *self = k;
            return true;
        }
        false
    }
}

pub fn tokenize(mut text: &str) -> Result<Vec<Token>, String> {
    let mut result = vec![];
    loop {
        if text.is_empty() {
            return Ok(result);
        }
        if text.eat_prefix("forall") {
            result.push(Kw(Forall));
            continue;
        }
        let c = text.eat_char();
        if c.is_whitespace() {
            continue;
        }
        if c.is_alphabetic() {
            let mut ident = c.to_string();
            while text.pick_char().map(|x| x.is_alphanumeric() || x == '_') == Some(true) {
                ident.push(text.eat_char());
            }
            result.push(Ident(ident));
            continue;
        }
        if c == '_' {
            let mut num = 0;
            while let Some(d) = text.pick_char().and_then(|x| x.to_digit(10)) {
                text.eat_char();
                num = num * 10 + d as usize;
            }
            result.push(Wild(num));
            continue;
        }
        if let Some(d) = c.to_digit(10) {
            let mut num = d;
            while let Some(d) = text.pick_char().and_then(|x| x.to_digit(10)) {
                text.eat_char();
                num = num * 10 + d;
            }
            result.push(Number(num));
            continue;
        }
        result.push(Sign(c.to_string()));
        //return Err("Failed to tokenize".to_string());
    }
}
