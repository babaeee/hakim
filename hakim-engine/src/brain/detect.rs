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
pub fn detect_string(term: &Term) -> Option<String> {
    fn generate_reverse_string(t: &Term) -> Option<String> {
        if let Term::App { func, op: op2 } = t {
            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                if unique_name == "nil" && detect_char_ty(op2) {
                    return Some("".to_string());
                }
            }
            if let Term::App { func, op: op1 } = func.as_ref() {
                if let Term::App { func, op: ty } = func.as_ref() {
                    if detect_char_ty(ty) {
                        if let Term::Axiom { unique_name, .. } = func.as_ref() {
                            if unique_name == "cons" {
                                let c = detect_char(&op1)?;
                                let mut s = generate_reverse_string(&op2)?;
                                s.push(c);
                                return Some(s);
                            }
                        }
                    }
                }
            }
        }
        None
    }
    let s = generate_reverse_string(term)?;
    let s = s.chars().rev().collect::<String>();
    return Some(s);
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

pub fn detect_set_ty(ty: &Term) -> Option<TermRef> {
    if let Term::App { func, op } = ty {
        if let Term::Axiom { unique_name, .. } = func.as_ref() {
            if unique_name == "set" {
                return Some(op.clone());
            }
        }
    }
    None
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
pub fn detect_char_ty(ty: &Term) -> bool {
    if let Term::Axiom { unique_name, .. } = ty {
        if unique_name == "char" {
            return true;
        }
    }
    false
}
pub fn detect_z_ty(ty: &Term) -> bool {
    if let Term::Axiom { unique_name, .. } = ty {
        if unique_name == "ℤ" {
            return true;
        }
    }
    false
}

pub fn detect_r_ty(ty: &Term) -> bool {
    if let Term::Axiom { unique_name, .. } = ty {
        if unique_name == "ℝ" {
            return true;
        }
    }
    false
}
pub fn detect_q_set(ty: &Term) -> bool {
    if let Term::Axiom { unique_name, .. } = ty {
        if unique_name == "ℚ" {
            return true;
        }
    }
    false
}

pub fn detect_pair(t: &Term) -> Option<(TermRef, TermRef, TermRef, TermRef)> {
    if let Term::App { func, op: op2 } = t {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: ty2 } = func.as_ref() {
                if let Term::App { func, op: ty1 } = func.as_ref() {
                    if let Term::Axiom { unique_name, .. } = func.as_ref() {
                        if unique_name == "pair" {
                            return Some((op1.clone(), op2.clone(), ty1.clone(), ty2.clone()));
                        }
                    }
                }
            }
        }
    }
    None
}

pub fn detect_tuple_items(mut t: TermRef) -> Option<Vec<TermRef>> {
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
