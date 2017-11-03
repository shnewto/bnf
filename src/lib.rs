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
//!     let grammar = bnf::parse(input);
//!     println!("{:#?}", grammar);
//! }
//! ```
//!

#[macro_use]
extern crate nom;
extern crate rand;
mod parsers;
mod reports;
mod generate;
pub mod node;
use node::{Grammar, Term};
use nom::IResult;

/// Parse a BNF grammer
pub fn parse(input: &str) -> Grammar {
    match parsers::grammar(input.as_bytes()) {
        IResult::Done(_, o) => return o,
        IResult::Error(e) => {
            reports::report_error(e);
        }
        IResult::Incomplete(n) => reports::report_incomplete(n, input.len()),
    }

    Grammar::new()
}

pub fn generate(grammar: Grammar) -> String {
    let lhs = grammar.productions_iter().nth(0).unwrap().lhs.clone();
    let start_rule: String;
    match lhs {
        Term::Nonterminal(nt) => start_rule = nt,
        _ => start_rule = String::from(""),
    }
    generate::traverse(grammar, start_rule)
}
