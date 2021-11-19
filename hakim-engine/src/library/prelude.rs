use crate::{app_ref, brain::Term, term_ref, TermRef};

pub fn u() -> TermRef {
    term_ref!(universe 0)
}
pub fn u1() -> TermRef {
    term_ref!(universe 1)
}
pub fn u2() -> TermRef {
    term_ref!(universe 2)
}
pub fn u3() -> TermRef {
    term_ref!(universe 3)
}
pub fn z() -> TermRef {
    term_ref!(axiom "ℤ" , u())
}
pub fn false_ty() -> TermRef {
    term_ref!(axiom "False" , u())
}
fn v0() -> TermRef {
    term_ref!(v 0)
}
fn v1() -> TermRef {
    term_ref!(v 1)
}
pub fn eq() -> TermRef {
    term_ref!(axiom "eq" , forall u(), forall v0(), forall v1(), u())
}
pub fn lt() -> TermRef {
    term_ref!(axiom "lt" , forall z(), forall z(), u())
}
pub fn plus() -> TermRef {
    term_ref!(axiom "plus", forall z(), forall z(), z())
}
pub fn mult() -> TermRef {
    term_ref!(axiom "mult", forall z(), forall z(), z())
}
pub fn ex() -> TermRef {
    term_ref!(axiom "ex", forall u(), forall term_ref!(forall v0(), u()), u())
}
pub fn or() -> TermRef {
    term_ref!(axiom "or", forall u(), forall u(), u())
}
pub fn and() -> TermRef {
    term_ref!(axiom "and", forall u(), forall u(), u())
}
pub fn set() -> TermRef {
    term_ref!(axiom "set", forall u(), u())
}
//∀ x0: U, (x0 → U) → set x0
pub fn set_from_func() -> TermRef {
    term_ref!(axiom "set_from_func", forall u(),
        forall term_ref!(forall v0(), u()), app_ref!(set(), v1()))
}
