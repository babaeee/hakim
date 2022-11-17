use num_bigint::BigInt;

use super::{good_char, Term, TermRef};

pub fn detect_char(term: &Term) -> Option<char> {
    if let Term::App { func, op } = term {
        if let Term::Axiom { unique_name, .. } = func.as_ref() {
            if unique_name == "chr" {
                if let Term::Number { value } = op.as_ref() {
                    let v = value % BigInt::from(256i32);
                    let c = char::from(u8::try_from(v).unwrap());
                    if good_char(c) {
                        return Some(c);
                    }
                }
            }
        }
    }
    None
}

pub fn detect_len(t: &Term) -> Option<(TermRef, TermRef)> {
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

pub fn detect_list_ty(ty: &Term) -> Option<TermRef> {
    if let Term::App { func, op } = ty {
        if let Term::Axiom { unique_name, .. } = func.as_ref() {
            if unique_name == "list" {
                return Some(op.clone());
            }
        }
    }
    None
}
