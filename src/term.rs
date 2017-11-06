use std::fmt;
use std::str;
use nom::IResult;
use parsers;
use error::Error;

/// A Term can represent a Terminal or Nonterminal node
#[derive(PartialEq, Debug, Clone)]
pub enum Term {
    Terminal(String),
    Nonterminal(String),
}

impl Term {
    // Get `Term` by parsing a string
    pub fn from_parse(s: &str) -> Result<Self, Error> {
        match parsers::term_complete(s.as_bytes()) {
            IResult::Done(_, o) => Ok(o),
            IResult::Incomplete(n) => Err(Error::from(n)),
            IResult::Error(e) => Err(Error::from(e)),
        }
    }
}

impl str::FromStr for Term {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_parse(s)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Term::Terminal(ref s) => write!(f, "\"{}\"", s),
            Term::Nonterminal(ref s) => write!(f, "<{}>", s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn parse_complete() {
        assert_eq!(
            Ok(Term::Nonterminal(String::from("dna"))),
            Term::from_str("<dna>")
        );
    }

    #[test]
    fn parse_incomplete() {
        let incomplete = Term::from_str("<dna");
        assert!(incomplete.is_err());

        let error = incomplete.unwrap_err();
        match error {
            Error::ParseError(ref s) => assert!(s.starts_with("Parsing error:")),
            _ => panic!("Incomplete term should be parse error"),
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
}
