#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AbsSign {
    Forall,
    Fun,
    Exists,
}

impl Display for AbsSign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            AbsSign::Forall => '∀',
            AbsSign::Fun => 'λ',
            AbsSign::Exists => '∃',
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Char(char),
    Ident(String),
    Abs(AbsSign),
    Sign(String),
    Number(BigInt),
    Wild(Option<String>),
}

use std::fmt::{Display, Write};

use num_bigint::BigInt;
use Token::*;

trait Eater {
    fn pick_char(&self) -> Option<char>;
    fn eat_char(&mut self) -> Result<char, String>;
    fn eat_prefix(&mut self, prefix: &str) -> bool;
}

impl Eater for &str {
    fn pick_char(&self) -> Option<char> {
        self.chars().next()
    }

    fn eat_char(&mut self) -> Result<char, String> {
        let c = self
            .chars()
            .next()
            .ok_or_else(|| "unexpected end of file".to_string())?;
        *self = &self[c.len_utf8()..];
        Ok(c)
    }

    fn eat_prefix(&mut self, prefix: &str) -> bool {
        if let Some(k) = self.strip_prefix(prefix) {
            *self = k;
            return true;
        }
        false
    }
}

pub fn is_valid_ident_first_char(c: char) -> bool {
    c.is_alphabetic()
}

pub fn is_valid_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

pub fn is_whity_char(c: char) -> bool {
    c.is_whitespace() || c == '\u{2068}' || c == '\u{2069}'
}

pub fn is_valid_ident(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    if !is_valid_ident_first_char(chars.next().unwrap()) {
        return false;
    }
    chars.all(is_valid_ident_char)
}

pub fn tokenize(mut text: &str) -> Result<Vec<Token>, String> {
    let mut result = vec![];
    loop {
        if text.is_empty() {
            return Ok(result);
        }
        if text.eat_prefix("∀") {
            result.push(Abs(AbsSign::Forall));
            continue;
        }
        if text.eat_prefix("∃") {
            result.push(Abs(AbsSign::Exists));
            continue;
        }
        if text.eat_prefix("λ") {
            result.push(Abs(AbsSign::Fun));
            continue;
        }
        if text.eat_prefix("<->") {
            result.push(Sign("↔".to_string()));
            continue;
        }
        if text.eat_prefix("->") {
            result.push(Sign("→".to_string()));
            continue;
        }
        if text.eat_prefix("++") {
            result.push(Sign("++".to_string()));
            continue;
        }
        let c = text.eat_char()?;
        if is_whity_char(c) {
            continue;
        }
        if is_valid_ident_first_char(c) {
            let mut ident = c.to_string();
            while text.pick_char().map(is_valid_ident_char) == Some(true) {
                ident.push(text.eat_char()?);
            }
            result.push(match ident.as_str() {
                "forall" => Abs(AbsSign::Forall),
                "exists" => Abs(AbsSign::Exists),
                "fn" => Abs(AbsSign::Fun),
                "mod" => Sign(ident),
                _ => Ident(ident),
            });
            continue;
        }
        if c == '\'' {
            let c = text.eat_char()?;
            let end = text.eat_char()?;
            if end != '\'' {
                return Err("invalid char end".to_string());
            }
            result.push(Char(c));
            continue;
        }
        if c == '?' {
            let mut name = match text.pick_char() {
                Some(c) if is_valid_ident_char(c) => {
                    text.eat_char()?;
                    c.to_string()
                }
                _ => {
                    result.push(Wild(None));
                    continue;
                }
            };
            while let Some(d) = text.pick_char() {
                if !is_valid_ident_char(d) {
                    break;
                }
                text.eat_char()?;
                name.push(d);
            }
            result.push(Wild(Some(name)));
            continue;
        }
        if let Some(d) = c.to_digit(10) {
            let mut num = d.into();
            while let Some(d) = text.pick_char().and_then(|x| x.to_digit(10)) {
                text.eat_char()?;
                num = num * 10 + d;
            }
            result.push(Number(num));
            continue;
        }
        result.push(Sign(c.to_string()));
        //return Err("Failed to tokenize".to_string());
    }
}
