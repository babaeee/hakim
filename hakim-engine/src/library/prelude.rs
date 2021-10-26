use crate::{app_ref, term_ref, TermRef};

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
pub fn v0() -> TermRef {
    term_ref!(v 0)
}
pub fn v1() -> TermRef {
    term_ref!(v 1)
}
pub fn eq() -> TermRef {
    term_ref!(axiom "eq" , forall u(), forall v0(), forall v1(), u())
}
pub fn lt() -> TermRef {
    term_ref!(axiom "lt" , forall z(), forall z(), u())
}
pub fn eq_refl() -> TermRef {
    term_ref!(axiom "eq_refl" , forall u(), forall v0(), app_ref!(eq(), v1(), v0(), v0()))
}
pub fn plus() -> TermRef {
    term_ref!(axiom "plus", forall z(), forall z(), z())
}
pub fn mult() -> TermRef {
    term_ref!(axiom "mult", forall z(), forall z(), z())
}
