#![doc = include_str!("../README.md")]

mod append_vec;
mod earley;
mod error;
mod expression;
mod generation;
mod grammar;
mod parser;
mod parsers;
mod production;
mod term;
mod tracing;
mod validation;
pub use crate::error::Error;
pub use crate::expression::Expression;
pub use crate::generation::{
    CoverageGuided, DepthBounded, GenerationStrategy, RandomWalk, Weighted,
};
pub use crate::grammar::{Grammar, ParseTree, ParseTreeNode, escape_mermaid_label};
pub use crate::parser::GrammarParser;
pub use crate::production::Production;
pub use crate::term::Term;

// The version of `rand` used by the public API.
pub use rand;

#[cfg(feature = "ABNF")]
pub use parsers::ABNF;
pub use parsers::{BNF, Format};

pub(crate) use hashbrown::HashMap;
pub(crate) use hashbrown::HashSet;
