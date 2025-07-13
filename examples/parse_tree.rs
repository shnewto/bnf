//! Example: Parse a tree from input using a Grammar
//!
//! This example demonstrates how to use a Grammar to parse an input string and print the resulting parse tree(s).
//! It uses the DNA grammar from the README and parses the input "GATTACA".

#![allow(clippy::print_stdout, clippy::print_stderr)]

use bnf::Grammar;

fn main() {
    // Define a simple BNF grammar for DNA sequences
    let bnf_input = r#"
        <dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'
    "#;

    // Parse the BNF string into a Grammar object
    let grammar: Grammar = match bnf_input.parse() {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Failed to create grammar from BNF string: {e}");
            return;
        }
    };

    // Input string to parse
    let sentence = "GATTACA";
    println!("Parsing input: {sentence}");

    // Parse the input string using the grammar
    let mut parse_trees = grammar.parse_input(sentence);
    match parse_trees.next() {
        Some(parse_tree) => {
            println!("Parse tree:\n{parse_tree}");
        }
        None => {
            println!("Grammar could not parse the sentence");
        }
    }
}
