use std::iter;

use super::Result;
use crate::{
    analysis::logic::{LogicArena, LogicBuilder, LogicTree, LogicValue},
    brain::{Term, TermRef},
    interactive::Frame,
};

#[derive(Debug, Clone, PartialEq, Eq)]
enum ListPart {
    Atom(TermRef),
    Element(TermRef),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ListItem(Vec<ListPart>);

#[derive(Debug, Clone)]
enum ListStatement {
    IsEq(ListItem, ListItem),
    IsNeq(ListItem, ListItem),
}

fn list_item_from_term(t: TermRef) -> ListItem {
    fn f(t: TermRef) -> Box<dyn Iterator<Item = ListPart>> {
        if let Term::App { func, op: op2 } = t.as_ref() {
            match func.as_ref() {
                Term::Axiom { unique_name, .. } => {
                    if unique_name == "nil" {
                        return Box::new(iter::empty());
                    }
                }
                Term::App { func, op: op1 } => {
                    match func.as_ref() {
                        Term::Axiom { unique_name, .. } => {
                            if unique_name == "tail" {
                                let mut list = f(op2.clone());
                                if let Some(first) = list.next() {
                                    match first {
                                        ListPart::Element(_) => return Box::new(list),
                                        /*ListPart::Atom(_x) => {
                                            todo!();
                                            /*let tail_of_first = Term::App {
                                                func: Term::App {
                                                    func: TermRef::Axiom {
                                                        ty: axiom_ty,
                                                        unique_name: unique_name,
                                                    },
                                                    op: op1,
                                                },
                                                op: x,
                                            };
                                            //tail_of_first := tail op1 x
                                            return Box::new(
                                                iter::once(ListPart::Atom(tail_of_first))
                                                    .chain(list),
                                            );*/
                                        }*/
                                        _ => (),
                                    };
                                }
                            }
                        }
                        Term::App { func, op: _ } => {
                            if let Term::Axiom { unique_name, .. } = func.as_ref() {
                                match unique_name.as_str() {
                                    "cons" => {
                                        return Box::new(
                                            iter::once(ListPart::Element(op1.clone()))
                                                .chain(f(op2.clone())),
                                        );
                                    }
                                    "plus_list" => {
                                        return Box::new(f(op1.clone()).chain(f(op2.clone())));
                                    }
                                    "head" => {
                                        if let Some(first) = f(op2.clone()).next() {
                                            return match first {
                                                ListPart::Element(x) => {
                                                    Box::new(iter::once(ListPart::Atom(x)))
                                                    //becuse it just one number
                                                }
                                                _ => Box::new(iter::once(ListPart::Atom(t))),
                                                /*ListPart::Atom(_x) => {
                                                    todo!();
                                                    /*
                                                    let head_of_frist = Term::App {
                                                        func: Term::App {
                                                            func: Term::App {
                                                                func: Term::Axiom {
                                                                    ty: axiom_ty,
                                                                    unique_name: unique_name,
                                                                },
                                                                op: ty,
                                                            },
                                                            op: op1,
                                                        },
                                                        op: x,
                                                    };
                                                    //head_of_first = head ty op1 x
                                                    Box::new(iter::once(ListPart::Atom(t)))*/
                                                } */
                                            };
                                        }
                                    }
                                    _ => (),
                                }
                            }
                        }
                        _ => (),
                    }
                }
                _ => (),
            }
        }
        Box::new(iter::once(ListPart::Atom(t)))
    }
    ListItem(f(t).collect())
}

fn convert(term: TermRef, _: LogicArena<'_, ListStatement>) -> LogicValue<'_, ListStatement> {
    if let Term::App { func, op: op2 } = term.as_ref() {
        if let Term::App { func, op: op1 } = func.as_ref() {
            if let Term::App { func, op: _ } = func.as_ref() {
                if let Term::Axiom { unique_name, .. } = func.as_ref() {
                    if unique_name == "eq" {
                        let x1 = list_item_from_term(op1.clone());
                        let x2 = list_item_from_term(op2.clone());
                        if x1 == x2 {
                            return LogicValue::True;
                        }
                        if x1.0.is_empty() && matches!(x2.0.get(0), Some(ListPart::Element(_)))
                            || x2.0.is_empty() && matches!(x1.0.get(0), Some(ListPart::Element(_)))
                        {
                            return LogicValue::False;
                        }
                        return LogicValue::Exp(LogicTree::Atom(ListStatement::IsEq(x1, x2)));
                    }
                }
            }
        }
    }
    LogicValue::Exp(LogicTree::Unknown)
}

fn check_contradiction(_: &[ListStatement]) -> bool {
    false
}

fn negator(x: ListStatement) -> ListStatement {
    match x {
        ListStatement::IsEq(x, y) => ListStatement::IsNeq(x, y),
        ListStatement::IsNeq(x, y) => ListStatement::IsEq(x, y),
    }
}

pub fn auto_list(frame: Frame) -> Result<Vec<Frame>> {
    LogicBuilder::build_tactic("auto_list", frame, convert, check_contradiction, negator)
}

#[cfg(test)]
mod tests {
    use crate::interactive::tests::{run_interactive_to_end, run_interactive_to_fail};

    fn success(goal: &str) {
        run_interactive_to_end(goal, "intros\nauto_list");
    }

    fn fail(goal: &str) {
        run_interactive_to_fail(goal, "intros", "auto_list");
    }

    #[test]
    fn fail_basic() {
        fail(r#""" = "salam""#);
    }

    #[test]
    fn nil_with_nil() {
        success(r#"""++""="""#);
        success(r#"∀ A: Universe, ∀ l: list A, l ++ nil A = l"#);
        success(r#"∀ A: Universe, ∀ l: list A, nil A ++ l = l"#);
        fail(r#"∀ A: Universe, ∀ l: list A, ~ nil A = l"#);
        success(r#" ~ "salam" = "" "#);
    }

    #[test]
    fn string_concat() {
        success(r#""hello" ++ " " ++ "world" = "hello world""#);
    }
    #[test]
    fn list_head_tail() {
        success(r#"head 0 ([2, 3]) = 2"#);
        success("tail [2, 3, 4] = [3, 4]");
        fail("tail [2, 4, 5] = [(head 0 [4, 5]) , 5]")
    }
}
