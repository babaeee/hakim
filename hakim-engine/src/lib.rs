#![allow(clippy::enum_variant_names)]

pub(crate) mod analysis;
pub(crate) mod brain;
pub mod engine;
pub mod interactive;
pub mod library;
pub(crate) mod parser;
pub use parser::notation_list;
pub(crate) mod search;
pub(crate) use brain::{Abstraction, Term, TermRef};
pub use library::all_library_data;
