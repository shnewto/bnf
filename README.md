# bnf

[![.github/workflows/ci.yml](https://github.com/shnewto/bnf/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/shnewto/bnf/actions)
[![coveralls](https://coveralls.io/repos/github/shnewto/bnf/badge.svg?branch=main)](https://coveralls.io/github/shnewto/bnf?branch=main)
[![Crates.io Version](https://img.shields.io/crates/v/bnf.svg)](https://crates.io/crates/bnf)
[![Crates.io](https://img.shields.io/crates/d/bnf.svg)](https://crates.io/crates/bnf)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/shnewto/bnf/blob/main/LICENSE)

A library for parsing Backus–Naur form context-free grammars.

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

## Output

Take the following grammar for DNA sequences to be input to this library's
`parse` function.

```text
<dna> ::= <base> | <base> <dna>
<base> ::= "A" | "C" | "G" | "T"
```

The output is a `Grammar` object representing a tree that looks like this:

```text
Grammar {
    productions: [
        Production {
            lhs: Nonterminal(
                "dna"
            ),
            rhs: [
                Expression {
                    terms: [
                        Nonterminal(
                            "base"
                        )
                    ]
                },
                Expression {
                    terms: [
                        Nonterminal(
                            "base"
                        ),
                        Nonterminal(
                            "dna"
                        )
                    ]
                }
            ]
        },
        Production {
            lhs: Nonterminal(
                "base"
            ),
            rhs: [
                Expression {
                    terms: [
                        Terminal(
                            "A"
                        )
                    ]
                },
                Expression {
                    terms: [
                        Terminal(
                            "C"
                        )
                    ]
                },
                Expression {
                    terms: [
                        Terminal(
                            "G"
                        )
                    ]
                },
                Expression {
                    terms: [
                        Terminal(
                            "T"
                        )
                    ]
                }
            ]
        }
    ]
}

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

let sentence = "GATTACA";

let mut parse_trees = grammar.parse_input(sentence);
match parse_trees.next() {
    Some(parse_tree) => println!("{}", parse_tree),
    _ => println!("Grammar could not parse sentence"),
}
```
