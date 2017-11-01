use std::fmt;
use std::slice;
use super::Production;


#[derive(PartialEq, Debug, Clone)]
/// A Grammar is comprised of any number of Productions
pub struct Grammar {
    productions: Vec<Production>,
}

impl Grammar {
    pub fn new() -> Grammar {
        Grammar {
            productions: vec![],
        }
    }

    pub fn from_parts(v: Vec<Production>) -> Grammar {
        Grammar { productions: v }
    }

    pub fn productions_iter(&self) -> Iter {
        Iter {
            iterator: self.productions.iter(),
        }
    }

    pub fn add_production(&mut self, expr: Production) {
        self.productions.push(expr)
    }

    pub fn remove_production(&mut self, prod: &Production) -> Option<Production> {
        if let Some(pos) = self.productions.iter().position(|x| *x == *prod) {
            Some(self.productions.remove(pos))
        } else {
            None
        }
    }
}

impl fmt::Display for Grammar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}\n",
            self.productions
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

pub struct Iter<'a> {
    iterator: slice::Iter<'a, Production>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Production;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}
