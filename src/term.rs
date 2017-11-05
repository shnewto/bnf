use std::fmt;
use std::str;
use parsers;
use error::Error;

/// A Term can represent a Terminal or Nonterminal node
#[derive(PartialEq, Debug, Clone)]
pub enum Term {
    Terminal(String),
    Nonterminal(String),
}

impl str::FromStr for Term {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parsers::term(s.as_bytes())
            .to_result()
            .map_err(|e| Self::Err::from(e))
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
    fn parse_term() {
        assert_eq!(
            Ok(Term::Nonterminal(String::from("dna"))),
            Term::from_str("<dna>")
        );
    }

    #[test]
    fn parse_incomplete_term() {
        assert!(Term::from_str("<dna").is_err());
    }
}
