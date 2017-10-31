use std::fmt;
use super::Term;


#[derive(PartialEq, Debug, Clone)]
/// An Expression is comprised of any number of Terms
pub struct Expression {
    pub terms: Vec<Term>,
}

impl Expression {
    pub fn new() -> Expression {
        Expression { terms: vec![] }
    }

    pub fn from_parts(v: Vec<Term>) -> Expression {
        Expression { terms: v }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let display = self.terms
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(" ");

        write!(f, "{}", display)
    }
}
