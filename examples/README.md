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

A simple example showing how to use a `Grammar` to parse an input string and print the resulting parse tree.

**What it demonstrates:**

- Parsing a BNF grammar string into a `Grammar` object
- Parsing an input string (e.g., "GATTACA") using the grammar
- Printing the resulting parse tree or an error message

**Run with:**

```bash
cargo run --example parse_tree
```

**Expected output:**

- The input string being parsed
- The parse tree printed in a readable format, or a message if parsing fails 
