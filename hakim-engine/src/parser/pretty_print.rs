use crate::{parser::binop::BinOp, Term, TermRef};

pub fn term_pretty_print(
    term: TermRef,
    name_stack: &mut Vec<(String, usize)>,
    level: u8,
) -> String {
    if let Some((l, op, r)) = BinOp::detect(term.clone()) {
        let s = format!(
            "{} {} {}",
            term_pretty_print(l, name_stack, op.prec() - 1),
            op,
            term_pretty_print(r, name_stack, op.prec() - 1)
        );
        return if level < op.prec() {
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
                format!("u{}", index)
            }
        }
        Term::Forall { var_ty, body } => {
            let name = format!("x{}", name_stack.len());
            let var_ty_str = term_pretty_print(var_ty.clone(), name_stack, 98);
            name_stack.push((name.clone(), 0));
            let body_str = term_pretty_print(body.clone(), name_stack, 200);
            let (_, c) = name_stack.pop().unwrap();
            if c == 0 {
                format!("{} → {}", var_ty_str, body_str)
            } else {
                format!("∀ {}: {}, {}", name, var_ty_str, body_str)
            }
        }
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
                term_pretty_print(func.clone(), name_stack, 1),
                term_pretty_print(op.clone(), name_stack, 0)
            );
            if level < 1 {
                format!("({})", s)
            } else {
                s
            }
        }
        Term::Wild { index } => format!("_{}", index),
    }
}
