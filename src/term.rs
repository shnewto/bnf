use std::fmt;
use std::str::FromStr;
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
    pub fn from_str(s: &str) -> Result<Self, Error> {
        // this is a little weird, should we default to Nonterminal?
        // Seems like empty would correspond to a terminal that represents
        // the empty string.
        if s.len() == 0 {
            return Ok(Term::Terminal(String::from("")));
        }
        match parsers::term_complete(s.as_bytes()) {
            IResult::Done(_, o) => Ok(o),
            IResult::Incomplete(n) => Err(Error::from(n)),
            IResult::Error(e) => Err(Error::from(e)),
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
            Term::Terminal(ref s) => write!(f, "\"{}\"", s),
            Term::Nonterminal(ref s) => write!(f, "<{}>", s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn parse_empty() {
        let result = Term::from_str("");
        assert!(result.is_ok(), "{:?} should be ok", result);
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
