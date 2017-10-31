use std::fmt;
use super::Expression;
use super::Term;


#[derive(PartialEq, Debug, Clone)]
/// A Production is comprised of any number of Expressions
pub struct Production {
    pub lhs: Term,
    pub rhs: Vec<Expression>,
}

impl Production {
    pub fn new() -> Production {
        Production {
            lhs: Term::Nonterminal(String::new()),
            rhs: vec![],
        }
    }

    pub fn from_parts(t: Term, e: Vec<Expression>) -> Production {
        Production { lhs: t, rhs: e }
    }
}

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ::= {};",
            self.lhs.to_string(),
            self.rhs
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(" | ")
        )
    }
}
