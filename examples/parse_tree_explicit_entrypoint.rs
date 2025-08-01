//! Example: Parse a tree from input using a Grammar, specifing which production to start from
//!
//! This example demonstrates how to use a Grammar to parse an input string and print the resulting parse tree(s).
//! In this example, the grammar is take from the the DNA grammar from the README, but reversed. By default, parser
//! would assume that the input should be parsed with the first rule. This example demonstrates how
//! to parse the input "GATTACA" with the second rule <dna> instead
#![allow(clippy::print_stdout, clippy::print_stderr)]

use bnf::Grammar;

fn main() {
    // Define a simple BNF grammar for DNA sequences
    let bnf_input = r#"
        <base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>
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
    println!("Parsing input with <dna>: {sentence}");

    // Target to start from
    let target_production = bnf::Term::Nonterminal("dna".to_string());

    // Parse the input string using the grammar, trying to match the second <dna> target
    let mut parse_trees = grammar.parse_input_starting_with(sentence, &target_production);
    match parse_trees.next() {
        Some(parse_tree) => {
            println!("Parse tree:\n{parse_tree}");
        }
        None => {
            println!("Grammar could not parse the sentence");
        }
    }
}
