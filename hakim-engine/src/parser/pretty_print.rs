use std::cmp::min;

use crate::{app_ref, parser::binop::BinOp, term_ref, Abstraction, Term, TermRef};

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

fn detect_set_items(mut t: &Term) -> Option<Vec<TermRef>> {
    let mut r = vec![];
    loop {
        if let Some(item) = detect_set_singleton(t) {
            r.push(item);
            return Some(r);
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
                        return Some(r);
                    } else {
                        return None;
                    }
                }
                _ => return None,
            },
            _ => return None,
        }
    }
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

fn abstraction_pretty_print_inner(
    abs: &Abstraction,
    names: &mut (Vec<(String, usize)>, impl Fn(&str) -> bool),
) -> (String, String, String) {
    let Abstraction {
        var_ty,
        body,
        hint_name,
    } = abs;
    let name = if let Some(hint) = hint_name {
        generate_name(names, hint)
    } else {
        generate_name(names, "x")
    };
    let var_ty_str = term_pretty_print_inner(var_ty, names, (200, 200));
    names.0.push((name.clone(), 0));
    let body_str = term_pretty_print_inner(body, names, (200, 200));
    names.0.pop();
    (name, var_ty_str, body_str)
}

fn check_name(names: &(Vec<(String, usize)>, impl Fn(&str) -> bool), name: &str) -> bool {
    names.1(name) && names.0.iter().all(|x| x.0 != name)
}

fn generate_name(names: &(Vec<(String, usize)>, impl Fn(&str) -> bool), hint: &str) -> String {
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

fn abstraction_pretty_print(
    sign: &str,
    abs: &Abstraction,
    name_stack: &mut (Vec<(String, usize)>, impl Fn(&str) -> bool),
    should_paren: bool,
) -> String {
    let (name, var_ty_str, body_str) = abstraction_pretty_print_inner(abs, name_stack);
    if should_paren {
        format!("({} {}: {}, {})", sign, name, var_ty_str, body_str)
    } else {
        format!("{} {}: {}, {}", sign, name, var_ty_str, body_str)
    }
}

fn term_pretty_print_inner(
    term: &Term,
    names: &mut (Vec<(String, usize)>, impl Fn(&str) -> bool),
    level: (u8, u8),
) -> String {
    if let Some((ty, fun)) = detect_exists(term) {
        if let Term::Fun(abs) = fun.as_ref() {
            return abstraction_pretty_print("∃", abs, names, level.1 < 200);
        } else {
            let abs = Abstraction {
                body: app_ref!(fun, term_ref!(v 0)),
                hint_name: None,
                var_ty: ty,
            };
            return abstraction_pretty_print("∃", &abs, names, level.1 < 200);
        };
    }
    if let Some((_, fun)) = detect_set_fn(term) {
        if let Term::Fun(x) = fun.as_ref() {
            let (name, ty, body) = abstraction_pretty_print_inner(x, names);
            return format!("{{ {}: {} | {} }}", name, ty, body);
        }
    }
    if let Some(exp) = detect_set_items(term) {
        let r = exp
            .into_iter()
            .rev()
            .map(|x| term_pretty_print_inner(&x, names, (200, 200)))
            .collect::<Vec<_>>();
        return format!("{{{}}}", r.join(", "));
    }
    if let Some((l, op, r)) = BinOp::detect(term) {
        return if min(level.0, level.1) < op.prec() {
            format!(
                "({} {} {})",
                term_pretty_print_inner(&l, names, (200, op.level_left())),
                op,
                term_pretty_print_inner(&r, names, (op.level_right(), 200))
            )
        } else {
            format!(
                "{} {} {}",
                term_pretty_print_inner(&l, names, (level.0, op.level_left())),
                op,
                term_pretty_print_inner(&r, names, (op.level_right(), level.1))
            )
        };
    }
    match term {
        Term::Axiom { unique_name, .. } => unique_name.to_string(),
        Term::Universe { index } => {
            if *index == 0 {
                "U".to_string()
            } else {
                format!("U{}", index)
            }
        }
        Term::Forall(abs) => abstraction_pretty_print("∀", abs, names, level.1 < 200),
        Term::Fun(abs) => abstraction_pretty_print("λ", abs, names, level.1 < 200),
        Term::Var { index } => {
            if let Some(x) = names.0.iter_mut().rev().nth(*index) {
                x.1 += 1;
                x.0.clone()
            } else {
                format!("f{}", index - names.0.len())
            }
        }
        Term::Number { value } => value.to_string(),
        Term::App { func, op } => {
            let s = format!(
                "{} {}",
                term_pretty_print_inner(func, names, (1, 1)),
                term_pretty_print_inner(op, names, (0, 0))
            );
            if min(level.0, level.1) < 1 {
                format!("({})", s)
            } else {
                s
            }
        }
        Term::Wild { index, scope: _ } => format!("?w{}", index),
    }
}

pub fn term_pretty_print(term: &Term, contain_name: impl Fn(&str) -> bool) -> String {
    let r = term_pretty_print_inner(term, &mut (vec![], contain_name), (200, 200));
    if cfg!(test) {
        r
    } else {
        format!("\u{2068}{}\u{2069}", r)
    }
}
