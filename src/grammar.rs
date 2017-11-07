use std::fmt;
use std::str;
use std::slice;
use nom::IResult;
use expression::Expression;
use production::Production;
use term::Term;
use parsers;
use error::Error;
use rand::{thread_rng, Rng};
use stacker;

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

    // Get `Grammar` by parsing a string
    pub fn from_str(s: &str) -> Result<Self, Error> {
        match parsers::grammar_complete(s.as_bytes()) {
            IResult::Done(_, o) => Ok(o),
            IResult::Incomplete(n) => Err(Error::from(n)),
            IResult::Error(e) => Err(Error::from(e)),
        }
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

    /// Get iterator of the `Grammar`'s `Production`s
    pub fn productions_iter(&self) -> Iter {
        Iter {
            iterator: self.productions.iter(),
        }
    }

    /// Get mutable iterator of the `Grammar`'s `Production`s
    pub fn productions_iter_mut(&mut self) -> IterMut {
        IterMut {
            iterator: self.productions.iter_mut(),
        }
    }

    fn eval_terminal(&self, term: &Term) -> Result<String, Error> {
        match *term {
            Term::Nonterminal(ref nt) => self.traverse(&nt),
            Term::Terminal(ref t) => Ok(t.clone()),
        }
    }

    fn traverse(&self, ident: &String) -> Result<String, Error> {
        let stack_red_zone: usize = 32 * 1024; // 32KB
        if stacker::remaining_stack() <= stack_red_zone {
            return Err(Error::GenerateError(
                String::from("Infinite loop detected!"),
            ));
        }

        let nonterm = Term::Nonterminal(ident.clone());
        let mut result = String::new();
        let production;
        let find_lhs = self.productions_iter().find(|&x| x.lhs == nonterm);

        match find_lhs {
            Some(p) => production = p,
            None => return Ok(nonterm.to_string()),
        }

        let expression;
        let expressions = production.rhs_iter().collect::<Vec<&Expression>>();

        match thread_rng().choose(&expressions) {
            Some(e) => expression = e.clone(),
            None => {
                return Err(Error::GenerateError(
                    String::from("Couldn't select random Expression!"),
                ));
            }
        }

        for term in expression.terms_iter() {
            match self.eval_terminal(&term) {
                Ok(s) => result = result + &s,
                Err(e) => return Err(e),
            }
        }

        Ok(result)
    }

    /// Generate a random sentence from self.
    /// Begins from lhs of first production.
    ///
    /// # Example
    ///
    /// ```rust
    /// extern crate bnf;
    /// use bnf::Grammar;
    ///
    /// fn main() {
    ///     let input =
    ///         "<dna> ::= <base> | <base> <dna>
    ///         <base> ::= \"A\" | \"C\" | \"G\" | \"T\"";
    ///     let grammar = Grammar::from_str(input).unwrap();
    ///     let sentence = grammar.generate();
    ///     match sentence {
    ///         Ok(s) => println!("random sentence: {}", s),
    ///         Err(e) => println!("something went wrong: {}!", e)
    ///     }
    /// }
    /// ```
    pub fn generate(&self) -> Result<String, Error> {
        let start_rule: String;
        let lhs = self.productions_iter().nth(0);

        match lhs {
            Some(term) => match term.lhs {
                Term::Nonterminal(ref nt) => start_rule = nt.clone(),
                Term::Terminal(_) => {
                    return Err(Error::GenerateError(format!(
                        "Termainal type cannot define a production in '{}'!",
                        term
                    )));
                }
            },
            None => {
                return Err(Error::GenerateError(
                    String::from("Failed to get first production!"),
                ));
            }
        }

        self.traverse(&start_rule)
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
        Self::from_str(s)
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

    #[test]
    fn parse_incomplete() {
        let grammar = Grammar::from_str("<almost_grammar> ::= <test");
        assert!(grammar.is_err(), "{:?} should be error", grammar);
    }
}
