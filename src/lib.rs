#![doc = include_str!("../README.md")]

mod append_vec;
mod earley;
mod error;
mod expression;
mod grammar;
mod parsers;
mod augmented;
mod production;
mod term;
mod tracing;
pub use crate::error::Error;
pub use crate::expression::Expression;
pub use crate::grammar::{Grammar, ParseTree, ParseTreeNode};
pub use crate::production::Production;
pub use crate::term::Term;

pub use parsers::{Format, BNF};
pub use augmented::ABNF;

pub(crate) use hashbrown::HashMap;
