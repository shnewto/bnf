use std::fmt;
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
