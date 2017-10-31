use std::fmt;
use std::slice;
use super::Production;


#[derive(PartialEq, Debug, Clone)]
/// A Grammar is comprised of any number of Productions
pub struct Grammar {
    pub productions: Vec<Production>,
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

    pub fn productions(&self) -> Iter {
        Iter {
            iterator: self.productions.iter(),
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
