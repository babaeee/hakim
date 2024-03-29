use crate::{app_ref, term_ref, TermRef};

pub fn u() -> TermRef {
    term_ref!(universe 0)
}
pub fn z() -> TermRef {
    term_ref!(axiom "ℤ" , u())
}
pub fn r() -> TermRef {
    term_ref!(axiom "ℝ" , u())
}
pub fn false_ty() -> TermRef {
    term_ref!(axiom "False" , u())
}
pub fn true_ty() -> TermRef {
    term_ref!(axiom "True" , u())
}
fn v0() -> TermRef {
    term_ref!(v 0)
}
fn v1() -> TermRef {
    term_ref!(v 1)
}
fn v2() -> TermRef {
    term_ref!(v 2)
}
fn v3() -> TermRef {
    term_ref!(v 3)
}
pub fn eq() -> TermRef {
    term_ref!(axiom "eq" , forall u(), forall v0(), forall v1(), u())
}
pub fn lt() -> TermRef {
    term_ref!(axiom "lt" , forall u(), forall v0(), forall v1(), u())
}
pub fn plus() -> TermRef {
    term_ref!(axiom "plus" , forall u(), forall v0(), forall v1(), v2())
}
pub fn pow() -> TermRef {
    term_ref!(axiom "pow", forall u(), forall v0(), forall v1(), v2())
}
pub fn minus() -> TermRef {
    term_ref!(axiom "minus", forall u(), forall v0(), forall v1(), v2())
}
pub fn neg() -> TermRef {
    term_ref!(axiom "neg", forall u(), forall v0(), v1())
}
pub fn mult() -> TermRef {
    term_ref!(axiom "mult", forall u(), forall v0(), forall v1(), v2())
}
pub fn div() -> TermRef {
    term_ref!(axiom "div", forall u(), forall v0(), forall v1(), r())
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
pub fn pair() -> TermRef {
    term_ref!(axiom "pair", forall u(), forall u(), forall v1(), forall v1(), app_ref!(and(), v3(), v2()))
}
pub fn set() -> TermRef {
    term_ref!(axiom "set", forall u(), u())
}
//∀ x0: U, (x0 → U) → set x0
pub fn set_from_func() -> TermRef {
    term_ref!(axiom "set_from_func", forall u(),
        forall term_ref!(forall v0(), u()), app_ref!(set(), v1()))
}
pub fn set_empty() -> TermRef {
    term_ref!(axiom "set_empty", forall u(), app_ref!(set(), v0()))
}
pub fn set_singleton() -> TermRef {
    term_ref!(axiom "set_singleton", forall u(), forall v0(), app_ref!(set(), v1()))
}
pub fn finite() -> TermRef {
    term_ref!(axiom "finite", forall u(), forall app_ref!(set(), v0()), u())
}
pub fn q_set() -> TermRef {
    term_ref!(axiom "ℚ", app_ref!(set(), r()))
}
pub fn inset() -> TermRef {
    term_ref!(axiom "inset", forall u(), forall v0(), forall app_ref!(set(), v1()), u())
}
pub fn union() -> TermRef {
    term_ref!(axiom "union", forall u(), 
        forall app_ref!(set(), v0()), forall app_ref!(set(), v1()), app_ref!(set(), v2()))
}
pub fn intersection() -> TermRef {
    term_ref!(axiom "intersection", forall u(), 
        forall app_ref!(set(), v0()), forall app_ref!(set(), v1()), app_ref!(set(), v2()))
}
pub fn setminus() -> TermRef {
    term_ref!(axiom "setminus", forall u(), 
        forall app_ref!(set(), v0()), forall app_ref!(set(), v1()), app_ref!(set(), v2()))
}
pub fn included() -> TermRef {
    term_ref!(axiom "included", forall u(), 
        forall app_ref!(set(), v0()), forall app_ref!(set(), v1()), u())
}
pub fn len1() -> TermRef {
    term_ref!(axiom "len1", forall u(), forall v0(), z())
}
pub fn abs() -> TermRef {
    term_ref!(axiom "abs", forall r(), r())
}
pub fn list() -> TermRef {
    term_ref!(axiom "list", forall u(), u())
}
pub fn inlist() -> TermRef {
    term_ref!(axiom "inlist", forall u(), forall v0(), forall app_ref!(list(), v1()), u())
}
pub fn nil() -> TermRef {
    term_ref!(axiom "nil", forall u(), app_ref!(list(), v0()))
}
pub fn cons() -> TermRef {
    term_ref!(axiom "cons", forall u(), forall v0(), forall app_ref!(list(), v1()), 
            app_ref!(list(), v2()))
}
pub fn cnt() -> TermRef {
    term_ref!(axiom "cnt", forall u(), forall v0(), forall app_ref!(list(), v1()), z())
}
pub fn divide() -> TermRef {
    term_ref!(axiom "divide", forall z(), forall z(), u())
}
pub fn mod_of() -> TermRef {
    term_ref!(axiom "mod_of", forall z(), forall z(), z())
}
pub fn sigma() -> TermRef {
    term_ref!(axiom "sigma", forall z(), forall z(), forall term_ref!( forall z(), z()), z())
}
//∀ X Y Z: U, (Y → Z) → (X → Y) → (X → Z)
pub fn compos() -> TermRef {
    term_ref!(axiom "compos", forall u(), forall u(), forall u(), 
        forall term_ref!(forall v1(), v1()), 
        forall term_ref!(forall v3(), v3()),
        term_ref!(forall term_ref!(v 4), v3()))
}
pub fn char_ty() -> TermRef {
    term_ref!(axiom "char" , u())
}
pub fn chr() -> TermRef {
    term_ref!(axiom "chr", forall z(), char_ty())
}
pub fn to_universe() -> TermRef {
    term_ref!(axiom "to_universe", forall u(), forall v0(), u())
}
pub fn init_dict() -> im::HashMap<String, TermRef> {
    let mut name_dict = im::HashMap::<String, TermRef>::default();
    name_dict.insert("U".to_string(), u());
    name_dict.insert("ℤ".to_string(), z());
    name_dict.insert("ℝ".to_string(), r());
    name_dict.insert("ℚ".to_string(), q_set());
    name_dict.insert("False".to_string(), false_ty());
    name_dict.insert("True".to_string(), true_ty());
    name_dict.insert("div".to_string(), div());
    name_dict.insert("divide".to_string(), divide());
    name_dict.insert("eq".to_string(), eq());
    name_dict.insert("ex".to_string(), ex());
    name_dict.insert("plus".to_string(), plus());
    name_dict.insert("pow".to_string(), pow());
    name_dict.insert("minus".to_string(), minus());
    name_dict.insert("mod_of".to_string(), mod_of());
    name_dict.insert("mult".to_string(), mult());
    name_dict.insert("neg".to_string(), neg());
    name_dict.insert("div".to_string(), div());
    name_dict.insert("or".to_string(), or());
    name_dict.insert("lt".to_string(), lt());
    name_dict.insert("and".to_string(), and());
    name_dict.insert("pair".to_string(), pair());
    name_dict.insert("set".to_string(), set());
    name_dict.insert("set_from_func".to_string(), set_from_func());
    name_dict.insert("set_empty".to_string(), set_empty());
    name_dict.insert("set_singleton".to_string(), set_singleton());
    name_dict.insert("setminus".to_string(), setminus());
    name_dict.insert("list".to_string(), list());
    name_dict.insert("nil".to_string(), nil());
    name_dict.insert("cons".to_string(), cons());
    name_dict.insert("compos".to_string(), compos());
    name_dict.insert("cnt".to_string(), cnt());
    name_dict.insert("union".to_string(), union());
    name_dict.insert("inlist".to_string(), inlist());
    name_dict.insert("intersection".to_string(), intersection());
    name_dict.insert("inset".to_string(), inset());
    name_dict.insert("finite".to_string(), finite());
    name_dict.insert("included".to_string(), included());
    name_dict.insert("sigma".to_string(), sigma());
    name_dict.insert("len1".to_string(), len1());
    name_dict.insert("abs".to_string(), abs());
    name_dict.insert("char".to_string(), char_ty());
    name_dict.insert("chr".to_string(), chr());
    name_dict.insert("to_universe".to_string(), to_universe());
    name_dict
}
