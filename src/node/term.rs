use std::fmt;


#[derive(PartialEq, Debug, Clone)]
/// A Term can represent a Terminal or Nonterminal node
pub enum Term {
    Terminal(String),
    Nonterminal(String),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Term::Terminal(ref s) => write!(f, "\"{}\"", s),
            Term::Nonterminal(ref s) => write!(f, "<{}>", s),
        }
    }
}
