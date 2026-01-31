#![doc = include_str!("../README.md")]

mod append_vec;
mod earley;
mod error;
mod expression;
pub mod grammar;
mod parser;
mod parsers;
mod production;
mod term;
mod tracing;
pub use crate::error::Error;
pub use crate::expression::Expression;
pub use crate::grammar::{ParseTree, ParseTreeNode};
pub use crate::parser::GrammarParser;
pub use crate::production::Production;
pub use crate::term::Term;
pub use bnf_macros::grammar;

/// Grammar with owned (runtime-parsed) or borrowed (const) data.
/// This type alias is for the common case; use [`grammar::Grammar`] for a generic lifetime.
///
/// A local grammar can be used with [`grammar::Grammar::build_parser`]:
/// the parser borrows the grammar for its lifetime, so the grammar must outlive the parser.
/// For compile-time grammars, use [`grammar::Grammar::from_borrowed`]
/// with static data (see the `const_grammar` example).
pub type Grammar = crate::grammar::Grammar<'static>;

// The version of `rand` used by the public API.
pub use rand;

#[cfg(feature = "ABNF")]
pub use parsers::ABNF;
pub use parsers::{BNF, Format};

pub(crate) use hashbrown::HashMap;
