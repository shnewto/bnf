# bnf

[![Build Status](https://travis-ci.org/snewt/bnf.svg?branch=master)](https://travis-ci.org/snewt/bnf)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Crates.io Version](https://img.shields.io/crates/v/bnf.svg)](https://crates.io/crates/bnf)

A library for parsing Backus–Naur form context-free grammars
inspired by the JavaScript library [prettybnf](https://github.com/dhconnelly/prettybnf)

## What does a parsable BNF grammar look like?

The following grammar from the [Wikipedia page on Backus-Naur form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Example)
exemplifies a compatible grammar after adding ';' characters to indicate the end of each producion.

```text
<postal-address> ::= <name-part> <street-address> <zip-part>;

        <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
                    | <personal-part> <name-part>;

    <personal-part> ::= <initial> "." | <first-name>;

    <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>;

        <zip-part> ::= <town-name> "," <state-code> <ZIP-code> <EOL>;

<opt-suffix-part> ::= "Sr." | "Jr." | <roman-numeral> | "";
    <opt-apt-num> ::= <apt-num> | "";
```

## Output
Take the following grammar to be input to this library's `parse` function.
```
<A> ::= <B> | "C";
<B> ::= "D" | "E"; 
```

The output is a `Grammar` object representing a tree that looks like this:
```
Grammar {
    productions: [
        Production {
            lhs: Nonterminal(
                "A"
            ),
            rhs: [
                Expression {
                    terms: [
                        Nonterminal(
                            "B"
                        )
                    ]
                },
                Expression {
                    terms: [
                        Terminal(
                            "C"
                        )
                    ]
                }
            ]
        },
        Production {
            lhs: Nonterminal(
                "B"
            ),
            rhs: [
                Expression {
                    terms: [
                        Terminal(
                            "D"
                        )
                    ]
                },
                Expression {
                    terms: [
                        Terminal(
                            "E"
                        )
                    ]
                }
            ]
        }
    ]
}
```

## Example

```rust
extern crate bnf;

fn main() {
    let input =
        "<postal-address> ::= <name-part> <street-address> <zip-part>;

              <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
                            | <personal-part> <name-part>;

          <personal-part> ::= <initial> \".\" | <first-name>;

         <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>;

               <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>;

        <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\";
            <opt-apt-num> ::= <apt-num> | \"\";";

    let grammar = bnf::parse(input);
    println!("{:#?}", grammar);
}
```