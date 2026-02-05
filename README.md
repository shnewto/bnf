# bnf

[![.github/workflows/ci.yml](https://github.com/shnewto/bnf/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/shnewto/bnf/actions)
[![coveralls](https://coveralls.io/repos/github/shnewto/bnf/badge.svg?branch=main)](https://coveralls.io/github/shnewto/bnf?branch=main)
[![Crates.io Version](https://img.shields.io/crates/v/bnf.svg)](https://crates.io/crates/bnf)
[![Crates.io](https://img.shields.io/crates/d/bnf.svg)](https://crates.io/crates/bnf)
[![Documentation](https://docs.rs/bnf/badge.svg)](https://docs.rs/bnf)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/shnewto/bnf/blob/main/LICENSE)

A library for parsing Backus–Naur form context-free grammars.

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
bnf = "0.6"
```

## What does a parsable BNF grammar look like?

The following grammar from the
[Wikipedia page on Backus-Naur form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Example)
exemplifies a compatible grammar. (*Note: parser allows for an optional ';'
to indicate the end of a production)

```text
 <postal-address> ::= <name-part> <street-address> <zip-part>

      <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
                    | <personal-part> <name-part>

  <personal-part> ::= <initial> "." | <first-name>

 <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>

       <zip-part> ::= <town-name> "," <state-code> <ZIP-code> <EOL>

<opt-suffix-part> ::= "Sr." | "Jr." | <roman-numeral> | ""
    <opt-apt-num> ::= <apt-num> | ""
```

## Extended syntax (groups and optionals)

When parsing grammar text (e.g. [`str::parse`] or [`Grammar::parse_from`]), the parser accepts two shortcuts:

### Parenthesized groups `( ... )`

Group alternatives so they act as **one unit** in a sequence.

**Without parentheses**, `|` binds loosely. This rule:

```text
<s> ::= <a> | <b> <c>
```

means "`<a>` **or** `<b>` `<c>`". So `"a"` matches, and `"b c"` matches, but `"a c"` does not.

**With parentheses**, you get "(a or b) then c":

```text
<s> ::= (<a> | <b>) <c>
```

So only `"a c"` and `"b c"` match.

### Optionals `[ ... ]`

**Zero or one** of the grouped alternatives (like `?` in regex).

```text
<word> ::= <letter> [<digit>]
```

means: a letter, optionally followed by a digit. Both `"x"` and `"x1"` match.

Equivalent long form without extended syntax:

```text
<word>      ::= <letter> <opt-digit>
<opt-digit> ::= <digit> | ""
```

### Normalization

Groups and optionals are *normalized* into a grammar that uses only plain nonterminals and terminals: each group or optional is turned into a fresh internal nonterminal (e.g. `__anon0`, `__anon1`). The public [`Term`] type has only [`Term::Terminal`] and [`Term::Nonterminal`]; parsing and generation use this normalized form.

**Round-trip:** Formatting a grammar (e.g. `format!("{}", grammar)`) does *not* preserve `( )` or `[ ]`; the result uses `__anon*` names. Re-parsing yields an equivalent grammar.

Empty groups or optionals — `()` or `[]` with nothing inside — are invalid; at least one alternative is required.

## Output

Take the following grammar for DNA sequences to be input to this library's
`parse` function.

```text
<dna> ::= <base> | <base> <dna>
<base> ::= "A" | "C" | "G" | "T"
```

The output is a `Grammar` object representing a tree that looks like this:

```text
Grammar
├── <dna> ::=
│   ├── <base>
│   └── <base> <dna>
└── <base> ::=
    ├── "A"
    ├── "C"
    ├── "G"
    └── "T"
```

Once the `Grammar` object is populated, to generate a random sentence from it
call the object's generate function. `grammar.generate()`. For the above grammar
you could expect something like `TGGC` or `AG`.

If the generate function can't find a production for a nonterminal it tries
to evaluate it will print the identifer as a nonterminal, i.e. `<identifier>`.

The generate function will return an error if it detects an infinite loop caused
by a production such as `<PATTERN> ::= <PATTERN>`.

## Parse Example

```rust
use bnf::Grammar;

let input =
    "<postal-address> ::= <name-part> <street-address> <zip-part>

        <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
                        | <personal-part> <name-part>

    <personal-part> ::= <initial> '.' | <first-name>

    <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>

        <zip-part> ::= <town-name> ',' <state-code> <ZIP-code> <EOL>

    <opt-suffix-part> ::= 'Sr.' | 'Jr.' | <roman-numeral> | ''
        <opt-apt-num> ::= <apt-num> | ''";

let grammar: Result<Grammar, _> = input.parse();
match grammar {
    Ok(g) => println!("{:#?}", g),
    Err(e) => println!("Failed to make grammar from String: {}", e),
}
```

## Generate Example

```rust
use bnf::Grammar;

let input =
    "<dna> ::= <base> | <base> <dna>
    <base> ::= 'A' | 'C' | 'G' | 'T'";
let grammar: Grammar = input.parse().unwrap();
let sentence = grammar.generate();
match sentence {
    Ok(s) => println!("random sentence: {}", s),
    Err(e) => println!("something went wrong: {}!", e)
}
```

## Parse Sentence via Grammar

```rust
use bnf::Grammar;

let input =
    "<dna> ::= <base> | <base> <dna>
    <base> ::= 'A' | 'C' | 'G' | 'T'";
let grammar: Grammar = input.parse().unwrap();

// Create a parser from the grammar (validates all nonterminals are defined)
let parser = grammar.build_parser().unwrap();

let sentence = "GATTACA";

let mut parse_trees = parser.parse_input(sentence);
match parse_trees.next() {
    Some(parse_tree) => println!("{}", parse_tree),
    _ => println!("Grammar could not parse sentence"),
}
```

By default, `parse_input` implicitly starts from the first rule. To match another rule, 
`parse_input_starting_with` can be used:

```rust
use bnf::{Grammar, Term};

let input =
    "<dna> ::= <base> | <base> <dna>
    <base> ::= 'A' | 'C' | 'G' | 'T'";
let grammar: Grammar = input.parse().unwrap();

// Create a parser from the grammar (validates all nonterminals are defined)
let parser = grammar.build_parser().unwrap();

let sentence = "G";
let target_production = Term::Nonterminal("base".to_string());

let mut parse_trees = parser.parse_input_starting_with(sentence, &target_production);
match parse_trees.next() {
    Some(parse_tree) => println!("{}", parse_tree),
    _ => println!("Grammar could not parse sentence"),
}
```

