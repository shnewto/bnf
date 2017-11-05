use std::fmt;
use std::str;
use std::slice;
use production::Production;
use parsers;
use error::Error;

/// A Grammar is comprised of any number of Productions
#[derive(PartialEq, Debug, Clone)]
pub struct Grammar {
    productions: Vec<Production>,
}

impl Grammar {
    /// Construct a new `Grammar`
    pub fn new() -> Grammar {
        Grammar {
            productions: vec![],
        }
    }

    /// Construct an `Grammar` from `Production`s
    pub fn from_parts(v: Vec<Production>) -> Grammar {
        Grammar { productions: v }
    }

    /// Add `Production` to the `Grammar`
    pub fn add_production(&mut self, prod: Production) {
        self.productions.push(prod)
    }

    /// Remove `Production` from the `Grammar`
    pub fn remove_production(&mut self, prod: &Production) -> Option<Production> {
        if let Some(pos) = self.productions.iter().position(|x| *x == *prod) {
            Some(self.productions.remove(pos))
        } else {
            None
        }
    }

    /// Get iterator of the `Grammar`'s `Productions`s
    pub fn productions_iter(&self) -> Iter {
        Iter {
            iterator: self.productions.iter(),
        }
    }

    /// Get mutable iterator of the `Grammar`'s `Productions`s
    pub fn productions_iter_mut(&mut self) -> IterMut {
        IterMut {
            iterator: self.productions.iter_mut(),
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

impl str::FromStr for Grammar {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parsers::grammar(s.as_bytes())
            .to_result()
            .map_err(|e| Self::Err::from(e))
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

pub struct IterMut<'a> {
    iterator: slice::IterMut<'a, Production>,
}

impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Production;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use term::Term;
    use expression::Expression;
    use production::Production;

    #[test]
    fn new_grammars() {
        let lhs1: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs1: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p1: Production = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs2: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p2: Production = Production::from_parts(lhs2, vec![rhs2]);

        let mut g1: Grammar = Grammar::new();
        g1.add_production(p1.clone());
        g1.add_production(p2.clone());
        let g2: Grammar = Grammar::from_parts(vec![p1, p2]);
        assert_eq!(g1, g2);
    }

    #[test]
    fn add_production() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let production = Production::from_parts(lhs, expression_list);
        let productions = vec![production.clone()];
        let mut grammar = Grammar::new();

        // grammar starts empty
        assert_eq!(grammar.productions_iter().count(), 0);

        grammar.add_production(production.clone());

        // grammar now has production
        assert_eq!(grammar.productions_iter().count(), 1);

        // mutated grammar identical to new grammar built from same productions
        let filled_grammar = Grammar::from_parts(productions.clone());
        assert_eq!(grammar, filled_grammar);
    }

    #[test]
    fn remove_production() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let production = Production::from_parts(lhs, expression_list);
        let productions = vec![production.clone()];
        let mut grammar = Grammar::from_parts(productions.clone());

        // grammar has production
        assert_eq!(
            Some(&production),
            grammar.productions_iter().find(|&prod| *prod == production)
        );
        assert_eq!(grammar.productions_iter().count(), productions.len());

        // production has been removed
        let removed = grammar.remove_production(&production);
        assert_eq!(removed, Some(production.clone()));
        assert_eq!(grammar.productions_iter().count(), productions.len() - 1);
        assert_eq!(
            None,
            grammar.productions_iter().find(|&prod| *prod == production)
        );
    }

    #[test]
    fn remove_nonexistent_production() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let production = Production::from_parts(lhs, expression_list);
        let productions = vec![production.clone()];
        let mut grammar = Grammar::from_parts(productions.clone());

        let unused = Production::from_parts(Term::Nonterminal(String::from("nonexistent")), vec![]);

        // grammar has original production
        assert_eq!(
            Some(&production),
            grammar.productions_iter().find(|&prod| *prod == production)
        );
        assert_eq!(grammar.productions_iter().count(), productions.len());

        // unused production is not removed
        let removed = grammar.remove_production(&unused);
        assert_eq!(removed, None);
        assert_eq!(grammar.productions_iter().count(), productions.len());
        assert_eq!(
            None,
            grammar.productions_iter().find(|&prod| *prod == unused)
        );
    }
}
