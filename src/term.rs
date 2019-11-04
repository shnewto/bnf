#![allow(clippy::should_implement_trait)]

use error::Error;
use parsers;
use std::fmt;
use std::str::FromStr;

/// A Term can represent a Terminal or Nonterminal node
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Term {
    Terminal(String),
    Nonterminal(String),
}

impl Term {
    // Get `Term` by parsing a string
    pub fn from_str(s: &str) -> Result<Self, Error> {
        match parsers::term_complete(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

impl FromStr for Term {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str(s)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Term::Terminal(ref s) => {
                if s.contains('"') {
                    write!(f, "'{}'", s)
                } else {
                    write!(f, "\"{}\"", s)
                }
            }
            Term::Nonterminal(ref s) => write!(f, "<{}>", s),
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate quickcheck;

    use self::quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
    use super::*;

    impl Arbitrary for Term {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
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
            _ => TestResult::error(format!("{} to string and back should be safe", term)),
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
        match error {
            Error::ParseError(ref s) => assert!(s.starts_with("Parsing error:")),
            _ => panic!("Incomplete term should be parse error"),
        }
    }

    #[test]
    fn parse_incomplete() {
        let result = Term::from_str("");
        assert!(result.is_err(), "{:?} should be err", result);
        match result {
            Err(e) => match e {
                Error::ParseError(_) => (),
                e => panic!("should should be Error::ParseError: {:?}", e),
            },
            Ok(s) => panic!("should should be Error::ParseError: {}", s),
        }
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
            Term::from_str(&format!("<{}>", some_space))
        );
    }

    #[test]
    fn parse_whitespace_term() {
        let some_space = String::from(" some space ");
        assert_eq!(
            Ok(Term::Terminal(some_space.clone())),
            Term::from_str(&format!("\"{}\"", some_space))
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
}
