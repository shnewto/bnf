//! Build a static grammar at compile time using the `grammar!` macro.
//!
//! Same grammar as the DNA example in the README: `grammar!` expands to
//! code that builds a `Grammar` from borrowed static data (no allocation at runtime).

#![allow(clippy::print_stdout)]

use bnf::Grammar;

static DNA_GRAMMAR: Grammar = bnf::grammar! {
    <dna> ::= <base> | <base> <dna>;
    <base> ::= "A" | "C" | "G" | "T";
};

fn main() {
    let parser = DNA_GRAMMAR.build_parser().expect("grammar is valid");
    let parse_trees: Vec<_> = parser.parse_input("GATTACA").collect();
    match parse_trees.first() {
        Some(tree) => println!("{tree}"),
        None => println!("No parse"),
    }
}
