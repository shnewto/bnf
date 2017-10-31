use std::fmt;
use std::slice;
use super::Term;


#[derive(PartialEq, Debug, Clone)]
/// An Expression is comprised of any number of Terms
pub struct Expression {
    terms: Vec<Term>,
}

impl Expression {
    pub fn new() -> Expression {
        Expression { terms: vec![] }
    }

    pub fn from_parts(v: Vec<Term>) -> Expression {
        Expression { terms: v }
    }

    pub fn terms(&self) -> Iter {
        Iter {
            iterator: self.terms.iter(),
        }
    }

    pub fn add_term(&mut self, term: Term) {
        self.terms.push(term)
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

pub struct Iter<'a> {
    iterator: slice::Iter<'a, Term>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Term;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}
