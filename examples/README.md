# Examples

This directory contains examples demonstrating how to use the `bnf` library.

## Available Examples

### `create_grammar`

A simple example showing how to create a `Grammar` object from a BNF string.

**What it demonstrates:**

- Parsing a BNF grammar string into a `Grammar` object
- Displaying the grammar structure
- Using the grammar to generate random sentences

**Run with:**

```bash
cargo run --example create_grammar
```

**Expected output:**

- The grammar structure printed in a readable format
- A randomly generated DNA sequence (like "GA", "T", "ACGT", etc.)

This example uses the DNA grammar from the main README:

```bnf
<dna> ::= <base> | <base> <dna>
<base> ::= 'A' | 'C' | 'G' | 'T'
```

### `parse_tree`

A simple example showing how to use a `GrammarParser` to parse an input string and print the resulting parse tree.

**What it demonstrates:**

- Parsing a BNF grammar string into a `Grammar` object
- Creating a `GrammarParser` from the grammar (validates all nonterminals are defined)
- Parsing an input string (e.g., "GATTACA") using the parser
- Printing the resulting parse tree or an error message

**Run with:**

```bash
cargo run --example parse_tree
```

**Expected output:**

- The input string being parsed
- The parse tree printed in a readable format, or a message if parsing fails

### `parse_tree_explicit_entrypoint`

An example showing how to use a `GrammarParser` to parse an input string starting from a specific nonterminal.

**What it demonstrates:**

- Parsing a BNF grammar string into a `Grammar` object
- Creating a `GrammarParser` from the grammar (validates all nonterminals are defined)
- Parsing an input string starting with a specific nonterminal using `parse_input_starting_with`
- Printing the resulting parse tree or an error message

**Run with:**

```bash
cargo run --example parse_tree_explicit_entrypoint
```

**Expected output:**

- The input string being parsed with the target nonterminal
- The parse tree printed in a readable format, or a message if parsing fails
