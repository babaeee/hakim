#![allow(clippy::enum_variant_names)]

pub mod brain;
pub mod engine;
mod library;
pub mod parser;

pub use brain::{Abstraction, Term, TermRef};
