use std::fmt;
use std::slice;
use super::Expression;
use super::Term;


#[derive(PartialEq, Debug, Clone)]
/// A Production is comprised of any number of Expressions
pub struct Production {
    pub lhs: Term,
    rhs: Vec<Expression>,
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

    pub fn rhs_iter(&self) -> Iter {
        Iter {
            iterator: self.rhs.iter(),
        }
    }

    pub fn add_to_rhs(&mut self, expr: Expression) {
        self.rhs.push(expr)
    }

    pub fn remove_from_rhs(&mut self, expr: &Expression) -> Option<Expression> {
        if let Some(pos) = self.rhs.iter().position(|x| *x == *expr) {
            Some(self.rhs.remove(pos))
        } else {
            None
        }
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

pub struct Iter<'a> {
    iterator: slice::Iter<'a, Expression>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Expression;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}
