use std::cmp::min;

use crate::{parser::binop::BinOp, Abstraction, Term, TermRef};

fn detect_exists(t: &TermRef) -> Option<(TermRef, TermRef)> {
    match t.as_ref() {
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

fn abstraction_pretty_print(
    sign: &str,
    abs: &Abstraction,
    name_stack: &mut Vec<(String, usize)>,
    should_paren: bool,
) -> String {
    let Abstraction { var_ty, body } = abs;
    let name = format!("x{}", name_stack.len());
    let var_ty_str = term_pretty_print(var_ty.clone(), name_stack, (200, 200));
    name_stack.push((name.clone(), 0));
    let body_str = term_pretty_print(body.clone(), name_stack, (200, 200));
    name_stack.pop();
    if should_paren {
        format!("({} {}: {}, {})", sign, name, var_ty_str, body_str)
    } else {
        format!("{} {}: {}, {}", sign, name, var_ty_str, body_str)
    }
}

pub fn term_pretty_print(
    term: TermRef,
    name_stack: &mut Vec<(String, usize)>,
    level: (u8, u8),
) -> String {
    if let Some((_, fun)) = detect_exists(&term) {
        if let Term::Fun(x) = fun.as_ref() {
            return abstraction_pretty_print("∃", x, name_stack, level.1 < 200);
        }
    }
    if let Some((l, op, r)) = BinOp::detect(&term) {
        let s = format!(
            "{} {} {}",
            term_pretty_print(l, name_stack, (level.0, op.prec() - 1)),
            op,
            term_pretty_print(r, name_stack, (op.prec() - 1, level.1))
        );
        return if min(level.0, level.1) < op.prec() {
            format!("({})", s)
        } else {
            s
        };
    }
    match term.as_ref() {
        Term::Axiom { unique_name, .. } => unique_name.to_string(),
        Term::Universe { index } => {
            if *index == 0 {
                "U".to_string()
            } else {
                format!("U{}", index)
            }
        }
        Term::Forall(abs) => abstraction_pretty_print("∀", abs, name_stack, level.1 < 200),
        Term::Fun(abs) => abstraction_pretty_print("λ", abs, name_stack, level.1 < 200),
        Term::Var { index } => {
            if let Some(x) = name_stack.iter_mut().rev().nth(*index) {
                x.1 += 1;
                x.0.clone()
            } else {
                format!("f{}", index - name_stack.len())
            }
        }
        Term::Number { value } => value.to_string(),
        Term::App { func, op } => {
            let s = format!(
                "{} {}",
                term_pretty_print(func.clone(), name_stack, (1, 1)),
                term_pretty_print(op.clone(), name_stack, (0, 0))
            );
            if min(level.0, level.1) < 1 {
                format!("({})", s)
            } else {
                s
            }
        }
        Term::Wild { index } => format!("_{}", index),
    }
}
