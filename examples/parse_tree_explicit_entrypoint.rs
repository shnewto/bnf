//! Example: Parse a tree from input using a `GrammarParser`, specifying which production to start from
//!
//! This example demonstrates how to use a `GrammarParser` to parse an input string and print the resulting parse tree(s).
//! In this example, the grammar is taken from the DNA grammar from the README, but reversed. By default, parser
//! would assume that the input should be parsed with the first rule. This example demonstrates how
//! to parse the input "GATTACA" with the second rule <dna> instead
#![allow(clippy::print_stdout, clippy::print_stderr)]

use bnf::{Grammar, Term};

fn main() {
    // Define a simple BNF grammar for DNA sequences
    let bnf_input = r#"
        <base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>
    "#;

    // Parse the BNF string into a Grammar object
    let grammar = match bnf_input.parse::<Grammar>() {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Failed to create grammar from BNF string: {e}");
            return;
        }
    };

    // Create a parser from the grammar (validates all nonterminals are defined)
    let parser = match grammar.build_parser() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Failed to create parser: {e}");
            return;
        }
    };

    // Input string to parse
    let sentence = "GATTACA";
    println!("Parsing input with <dna>: {sentence}");

    // Target to start from
    let target_production = Term::nonterminal("dna");

    // Parse the input string using the parser, starting with the <dna> nonterminal
    let mut parse_trees = parser.parse_input_starting_with(sentence, &target_production);
    match parse_trees.next() {
        Some(parse_tree) => {
            println!("Parse tree:\n{parse_tree}");
        }
        None => {
            println!("Grammar could not parse the sentence");
        }
    }
}
