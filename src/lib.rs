//! bnf, a library for parsing Backus–Naur form context-free grammars
//!
//! Inspired by the JavaScript library [prettybnf](https://github.com/dhconnelly/prettybnf)
//!
//!
//! The code is available on [Github](https://github.com/snewt/bnf)
//!
//! ## What does a parsable BNF grammar look like?
//!
//! The following grammar from the [Wikipedia page on Backus-Naur form]
//! (https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Example)
//! exemplifies a compatible grammar after adding ';'
//! characters to indicate the end of each producion.
//!
//! ```text
//! <postal-address> ::= <name-part> <street-address> <zip-part>;
//!
//!         <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
//!                     | <personal-part> <name-part>;
//!
//!     <personal-part> ::= <initial> "." | <first-name>;
//!
//!     <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>;
//!
//!         <zip-part> ::= <town-name> "," <state-code> <ZIP-code> <EOL>;
//!
//! <opt-suffix-part> ::= "Sr." | "Jr." | <roman-numeral> | "";
//!     <opt-apt-num> ::= <apt-num> | "";
//! ```
//!
//! ## Output
//! Take the following grammar to be input to this library's `parse` function:
//!
//! ```text
//! <A> ::= <B> | "C";
//! <B> ::= "D" | "E";
//! ```
//!
//! The output is a `Grammar` object representing a tree that looks like this:
//!
//! ```text
//! Grammar {
//!     productions: [
//!         Production {
//!             lhs: Nonterminal(
//!                 "A"
//!             ),
//!             rhs: [
//!                 Expression {
//!                     terms: [
//!                         Nonterminal(
//!                             "B"
//!                         )
//!                     ]
//!                 },
//!                 Expression {
//!                     terms: [
//!                         Terminal(
//!                             "C"
//!                         )
//!                     ]
//!                 }
//!             ]
//!         },
//!         Production {
//!             lhs: Nonterminal(
//!                 "B"
//!             ),
//!             rhs: [
//!                 Expression {
//!                     terms: [
//!                         Terminal(
//!                             "D"
//!                         )
//!                     ]
//!                 },
//!                 Expression {
//!                     terms: [
//!                         Terminal(
//!                             "E"
//!                         )
//!                     ]
//!                 }
//!             ]
//!         }
//!     ]
//! }
//! ```
//!
//! ## Example
//!
//! ```rust
//! extern crate bnf;
//! use bnf::Grammar;
//!
//! fn main() {
//!     let input =
//!         "<postal-address> ::= <name-part> <street-address> <zip-part>;
//!
//!               <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
//!                             | <personal-part> <name-part>;
//!
//!           <personal-part> ::= <initial> \".\" | <first-name>;
//!
//!          <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>;
//!
//!                <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>;
//!
//!         <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\";
//!             <opt-apt-num> ::= <apt-num> | \"\";";
//!
//!     let grammar = Grammar::from_parse(input);
//!     match grammar {
//!         Ok(g) => println!("{:#?}", g),
//!         Err(e) => println!("Failed to make grammar from String: {:?}", e),
//!     }
//! }
//! ```
//!

#[macro_use]
extern crate nom;
mod parsers;
mod error;
mod term;
mod expression;
mod production;
mod grammar;
pub use term::Term;
pub use expression::Expression;
pub use production::Production;
pub use grammar::Grammar;
