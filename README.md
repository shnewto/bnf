# bnf

[![Build Status](https://travis-ci.org/snewt/bnf.svg?branch=master)](https://travis-ci.org/snewt/bnf)
[![Coverage Status](https://coveralls.io/repos/github/snewt/bnf/badge.svg?branch=master)](https://coveralls.io/github/snewt/bnf?branch=master)
[![Crates.io Version](https://img.shields.io/crates/v/bnf.svg)](https://crates.io/crates/bnf)
[![Crates.io](https://img.shields.io/crates/d/bnf.svg)](https://crates.io/crates/bnf)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

A library for parsing Backus–Naur form context-free grammars
inspired by the JavaScript libraries [prettybnf](https://github.com/dhconnelly/prettybnf) and
[erratic](https://github.com/dhconnelly/erratic)

## What does a parsable BNF grammar look like?

The following grammar from the [Wikipedia page on Backus-Naur form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Example)
exemplifies a compatible grammar. (*Note: parser allows for an optional ';'
to indicate the end of each producion)

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
Take the following grammar for DNA sequences to be input to this library's `parse` function.
```
<dna> ::= <base> | <base> <dna>;
<base> ::= "A" | "C" | "G" | "T"
```

The output is a `Grammar` object representing a tree that looks like this:
```
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

The generate function will return an error if it detects an infinite loop caused
by a production such as `<PATTERN> := <PATTERN>`.

## Example

```rust
extern crate bnf;

fn main() {
    let input =
        "<postal-address> ::= <name-part> <street-address> <zip-part>

              <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
                            | <personal-part> <name-part>

          <personal-part> ::= <initial> \".\" | <first-name>

         <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>

               <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>

        <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\"
            <opt-apt-num> ::= <apt-num> | \"\"";

    let grammar = bnf::parse(input);
    println!("{:#?}", grammar);
    println!("{}", grammar.generate());
}
```