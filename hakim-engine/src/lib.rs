#![allow(clippy::enum_variant_names)]

pub(crate) mod brain;
pub mod engine;
pub mod interactive;
mod library;
pub(crate) mod parser;
pub(crate) mod search;
pub(crate) use brain::{Abstraction, Term, TermRef};
