#![allow(clippy::should_implement_trait)]

use crate::Production;
use crate::error::Error;
use crate::expression::Expression;
use crate::parsers;
use std::fmt;
use std::ops;
use std::str::FromStr;

use nom::Parser;
use nom::combinator::all_consuming;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A Term can represent a Terminal or Nonterminal node
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum Term {
    /// A term which cannot be expanded further via productions
    Terminal(String),
    /// A term which may be be expanded further via productions
    Nonterminal(String),
    /// A inline term specified with () or []
    AnonymousNonterminal(Vec<Expression>),
}

/// Creates a Terminal if the input is a string literal or a Nonterminal if the input is inside angle brackets
/// ```
/// bnf::term!("terminal");
/// bnf::term!(<nonterminal>);
/// ```
#[macro_export]
macro_rules! term {
    (<$ident:ident>) => {
        $crate::Term::Nonterminal(stringify!($ident).to_string())
    };
    ($ident:ident) => {
        $crate::Term::Terminal(stringify!($ident).to_string())
    };
    // another case for string literal
    ($ident:literal) => {
        $crate::Term::Terminal($ident.to_string())
    };
}

impl FromStr for Term {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match all_consuming(parsers::term).parse(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

impl ops::Add<Term> for Term {
    type Output = Expression;

    fn add(self, rhs: Self) -> Self::Output {
        Expression::from_parts(vec![self, rhs])
    }
}

impl ops::Add<Expression> for Term {
    type Output = Expression;
    fn add(self, mut rhs: Expression) -> Self::Output {
        rhs.add_term(self);
        rhs
    }
}

impl ops::Add<&Expression> for Term {
    type Output = Expression;
    fn add(self, rhs: &Expression) -> Self::Output {
        let mut new = Expression::new();
        for t in rhs.terms_iter() {
            new.add_term(t.clone());
        }
        new.add_term(self);
        new
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Term::Terminal(ref s) => {
                if s.contains('\'') {
                    write!(f, "\"{s}\"")
                } else {
                    write!(f, "'{s}'")
                }
            }
            Term::Nonterminal(ref s) => write!(f, "<{s}>"),
            Term::AnonymousNonterminal(ref exprs) => write!(
                f,
                "{}",
                Production::from_parts(
                    Term::Nonterminal("anon-nonterminal".to_owned()),
                    exprs.clone()
                )
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    impl Arbitrary for Term {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut term = String::arbitrary(g);
            if bool::arbitrary(g) {
                term = term.chars().filter(|&c| (c != '>')).collect();
                Term::Nonterminal(term)
            } else {
                if term.contains('"') {
                    term = term.chars().filter(|&c| c != '\'').collect();
                } else if term.contains('\'') {
                    term = term.chars().filter(|&c| c != '"').collect();
                }
                Term::Terminal(term)
            }
        }
    }

    fn prop_to_string_and_back(term: Term) -> TestResult {
        let to_string = term.to_string();
        let from_str = Term::from_str(&to_string);
        match from_str {
            Ok(from_term) => TestResult::from_bool(from_term == term),
            _ => TestResult::error(format!("{term} to string and back should be safe")),
        }
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new().quickcheck(prop_to_string_and_back as fn(Term) -> TestResult)
    }

    #[test]
    fn parse_complete() {
        assert_eq!(
            Ok(Term::Nonterminal(String::from("dna"))),
            Term::from_str("<dna>")
        );
    }

    #[test]
    fn parse_error() {
        let incomplete = Term::from_str("<dna");
        assert!(incomplete.is_err());

        let error = incomplete.unwrap_err();
        assert!(matches!(error, Error::ParseError(s) if s.starts_with("Parsing error: ")));
    }

    #[test]
    fn parse_incomplete() {
        let result = Term::from_str("");
        assert!(matches!(result, Err(Error::ParseError(_))));
    }

    #[test]
    fn parse_error_display() {
        let incomplete = Term::from_str("<dna");
        assert!(incomplete.is_err());

        let error = incomplete.unwrap_err().to_string();
        assert!(!error.is_empty());
    }

    #[test]
    fn parse_whitespace_nonterm() {
        let some_space = String::from(" some space ");
        assert_eq!(
            Ok(Term::Nonterminal(some_space.clone())),
            Term::from_str(&format!("<{some_space}>"))
        );
    }

    #[test]
    fn parse_whitespace_term() {
        let some_space = String::from(" some space ");
        assert_eq!(
            Ok(Term::Terminal(some_space.clone())),
            Term::from_str(&format!("\"{some_space}\""))
        );
    }

    #[test]
    fn parse_quote_term() {
        let quote_term = Term::from_str("'\"'");
        assert_eq!(Ok(Term::Terminal(String::from("\""))), quote_term);
    }

    #[test]
    fn parse_single_quote_term() {
        let quote_term = Term::from_str("\"'\"");
        assert_eq!(Ok(Term::Terminal(String::from("'"))), quote_term);
    }

    #[test]
    fn quote_term_to_string_and_back() {
        let quote = Term::Terminal(String::from("\""));
        let to_string = quote.to_string();
        let from_string = Term::from_str(&to_string);
        assert_eq!(Ok(Term::Terminal(String::from("\""))), from_string);
    }

    #[test]
    fn add_operator() {
        let t1 = Term::Terminal(String::from("terminal"));
        let nt1 = Term::Nonterminal(String::from("nonterminal"));
        let t2 = Term::Terminal(String::from("terminal"));
        let nt2 = Term::Nonterminal(String::from("nonterminal"));
        let t3 = Term::Terminal(String::from("terminal"));
        let nt3 = Term::Nonterminal(String::from("nonterminal"));
        let t4 = Term::Terminal(String::from("terminal"));
        let nt4 = Term::Nonterminal(String::from("nonterminal"));

        // term + term
        let e1 = Expression::from_parts(vec![nt1, t1]);
        let e2 = nt2 + t2;
        // term + &expression
        let e3_1 = Expression::from_parts(vec![nt3]);
        let e3 = t3 + &e3_1;
        //term + expression
        let e4_1 = Expression::from_parts(vec![nt4]);
        let e4 = t4 + e4_1;

        // Term get's pushed to the end of expression.
        // functionally identical, but different to eq
        // example:
        // nt3 | Expression::from_parts(vec![t3]) != Expression::from_parts(vec![nt3, t3])

        assert_eq!(e1, e2);
        assert_eq!(e1, e3);
        assert_eq!(e1, e4);
    }

    #[test]
    fn macro_terminal() {
        let terminal = term!("terminal");
        assert_eq!(Term::Terminal(String::from("terminal")), terminal);
    }

    #[test]
    fn macro_nonterminal() {
        let nonterminal = term!(<nonterminal>);
        assert_eq!(Term::Nonterminal(String::from("nonterminal")), nonterminal);
    }
}
