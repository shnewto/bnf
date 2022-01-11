#![allow(clippy::should_implement_trait)]

use error::Error;
use parsers;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::str::FromStr;
use std::ops;
use expression::Expression;

/// A Term can represent a Terminal or Nonterminal node
#[derive(Deserialize, Serialize, Clone, Debug, Eq, Hash, PartialEq)]
pub enum Term {
    Terminal(String),
    Nonterminal(String),
}

impl FromStr for Term {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parsers::term_complete(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

impl ops::BitOr<Term> for Term {
    type Output = Expression;

    fn bitor(self, rhs: Self) -> Self::Output {
        Expression::from_parts(vec![self, rhs])
    }
}

impl ops::BitOr<Expression> for Term {
    type Output = Expression;
    fn bitor(self, mut rhs: Expression) -> Self::Output {
        rhs.add_term(self);
        rhs
    }
}

impl ops::BitOr<&Expression> for Term {
    type Output = Expression;
    fn bitor(self, rhs: &Expression) -> Self::Output {
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

    #[test]
    fn or_operator() {
        let t1 = Term::Terminal(String::from("terminal"));
        let nt1 = Term::Nonterminal(String::from("nonterminal"));
        let t2 = Term::Terminal(String::from("terminal"));
        let nt2 = Term::Nonterminal(String::from("nonterminal"));
        let t3 = Term::Terminal(String::from("terminal"));
        let nt3 = Term::Nonterminal(String::from("nonterminal"));
        let t4 = Term::Terminal(String::from("terminal"));
        let nt4 = Term::Nonterminal(String::from("nonterminal"));

        let e1 = Expression::from_parts(vec![nt1, t1]);
        let e2 = nt2 | t2;
        let e3_1 = Expression::from_parts(vec![nt3]);
        let e3 = t3 | e3_1;
        let mut e4_1 = Expression::from_parts(vec![nt4]);
        let e4 = t4 | e4_1;

        // Term get's pushed to the end of expression.
        // functionally identical, but different to eq
        // example:
        // nt3 | Expression::from_parts(vec![t3]) != Expression::from_parts(vec![nt3, t3])

        assert_eq!(e1, e2);
        assert_eq!(e1, e3);
        assert_eq!(e1, e4);
    }
}
