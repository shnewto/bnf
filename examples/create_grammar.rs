//! Simple example of creating a Grammar from a BNF string
//!
//! This example demonstrates how to parse a BNF grammar string into a Grammar object.
//! It uses the DNA grammar example from the README.

#![allow(clippy::print_stdout, clippy::use_debug)]

use bnf::Grammar;

fn main() {
    // Define a simple BNF grammar for DNA sequences
    let bnf_input = r#"
        <dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'
    "#;

    // Parse the BNF string into a Grammar object
    let grammar: Result<Grammar, _> = bnf_input.parse();

    match grammar {
        Ok(g) => {
            println!("Successfully created Grammar!");
            println!("Grammar structure:");
            println!("{g:#?}");

            // Demonstrate that we can use the grammar
            println!("\nGenerating a random DNA sequence:");
            match g.generate() {
                Ok(sentence) => println!("Generated: {sentence}"),
                Err(e) => println!("Error generating: {e}"),
            }
        }
        Err(e) => println!("Failed to create grammar from BNF string: {e}"),
    }
}
