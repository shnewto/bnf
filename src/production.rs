#![allow(clippy::should_implement_trait)]

use crate::error::Error;
use crate::expression::Expression;
use crate::parsers;
use crate::term::Term;
use serde::{Deserialize, Serialize};
use std::fmt;

use std::str::FromStr;

/// A Production is comprised of any number of Expressions
#[derive(Deserialize, Serialize, Clone, Debug, Eq, Hash, PartialEq)]
pub struct Production {
    pub lhs: Term,
    rhs: Vec<Expression>,
}

impl Production {
    /// Construct a new `Production`
    pub fn new() -> Production {
        Production {
            lhs: Term::Nonterminal(String::new()),
            rhs: vec![],
        }
    }

    /// Construct an `Production` from `Expression`s
    pub fn from_parts(t: Term, e: Vec<Expression>) -> Production {
        Production { lhs: t, rhs: e }
    }

    /// Add `Expression` to the `Production`'s right hand side
    pub fn add_to_rhs(&mut self, expr: Expression) {
        self.rhs.push(expr);
    }

    /// Remove `Expression` from the `Production`'s right hand side
    ///
    /// If interested if `Expression` was removed, then inspect the returned `Option`.
    pub fn remove_from_rhs(&mut self, expr: &Expression) -> Option<Expression> {
        if let Some(pos) = self.rhs.iter().position(|x| *x == *expr) {
            Some(self.rhs.remove(pos))
        } else {
            None
        }
    }

    /// Get iterator of the `Production`'s right hand side `Expression`s
    pub fn rhs_iter(&self) -> Iter {
        Iter {
            slice: &self.rhs[..],
        }
    }

    /// Get mutable iterator of the `Production`'s right hand side `Expression`s
    pub fn rhs_iter_mut(&mut self) -> IterMut {
        IterMut {
            slice: &mut self.rhs[..],
        }
    }

    /// Get number of right hand side `Expression`s
    pub fn len(&self) -> usize {
        self.rhs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rhs.is_empty()
    }
}

impl Default for Production {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ::= {}",
            self.lhs,
            self.rhs
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join(" | ")
        )
    }
}

impl FromStr for Production {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parsers::production_complete(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Iter<'a> {
    slice: &'a [Expression],
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Expression;

    fn next(&mut self) -> Option<Self::Item> {
        self.slice.split_first().map(|(first, rest)| {
            self.slice = rest;
            first
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct IterMut<'a> {
    slice: &'a mut [Expression],
}

impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Expression;

    fn next(&mut self) -> Option<Self::Item> {
        let slice = std::mem::take(&mut self.slice);

        slice.split_first_mut().map(|(first, rest)| {
            self.slice = rest;
            first
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    impl Arbitrary for Production {
        fn arbitrary(g: &mut Gen) -> Self {
            let lhs_str = String::arbitrary(g)
                .chars()
                .filter(|&c| (c != '>'))
                .collect();

            let lhs = Term::Nonterminal(lhs_str);

            let mut rhs = Vec::<Expression>::arbitrary(g);
            if rhs.is_empty() {
                rhs.push(Expression::arbitrary(g));
            }
            Production { lhs, rhs }
        }
    }

    fn prop_to_string_and_back(prop: Production) -> TestResult {
        let to_string = prop.to_string();
        let from_str = Production::from_str(&to_string);
        match from_str {
            Ok(from_prod) => TestResult::from_bool(from_prod == prop),
            _ => TestResult::error(format!("{} to string and back should be safe", prop)),
        }
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new()
            .tests(1000)
            .gen(Gen::new(25usize))
            .quickcheck(prop_to_string_and_back as fn(Production) -> TestResult)
    }

    #[test]
    fn new_productions() {
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
        let mut p2: Production = Production::new();
        p2.lhs = lhs2;
        p2.add_to_rhs(rhs2);

        assert_eq!(p1, p2);
    }

    #[test]
    fn remove_from_rhs() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Nonterminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Nonterminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        // unnecessary expression to be removed from production
        let two_more = Expression::from_parts(vec![
            Term::Nonterminal(String::from("base")),
            Term::Nonterminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more, two_more.clone()];
        let mut production = Production::from_parts(lhs, expression_list.clone());
        let removed = production.remove_from_rhs(&two_more);

        // the removed element should be the accident
        assert_eq!(Some(two_more.clone()), removed);
        // number of productions should have decreased
        assert_eq!(production.rhs_iter().count(), expression_list.len() - 1);
        // the unnecessary should no longer be found
        assert_eq!(
            production
                .rhs_iter()
                .find(|&expression| *expression == two_more,),
            None
        );
    }

    #[test]
    fn remove_nonexistent_from_rhs() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Nonterminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let mut production = Production::from_parts(lhs, expression_list.clone());

        // unused expression to fail being removed from production
        let two_more = Expression::from_parts(vec![
            Term::Nonterminal(String::from("base")),
            Term::Nonterminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let removed = production.remove_from_rhs(&two_more);

        // the unused term should not be found in the terms
        assert_eq!(production.rhs_iter().find(|&expr| *expr == two_more), None);
        // no term should have been removed
        assert_eq!(None, removed);
        // number of terms should not have decreased
        assert_eq!(production.rhs_iter().count(), expression_list.len());
    }

    #[test]
    fn parse_complete() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Nonterminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Nonterminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let production = Production::from_parts(lhs, vec![last, one_more]);
        assert_eq!(
            Ok(production),
            Production::from_str("<dna> ::= <base> | <base> <dna>")
        );
    }

    #[test]
    fn parse_error() {
        let result = Production::from_str("<base> ::= \"A\" | \"C\" | \"G\" |");
        assert!(
            result.is_err(),
            "production result should be error {:?}",
            result
        );

        let production = result.unwrap_err();
        match production {
            Error::ParseError(_) => (),
            e => panic!("production error should be error: {:?}", e),
        }
    }

    #[test]
    fn parse_incomplete() {
        let result = Production::from_str("");
        assert!(result.is_err(), "{:?} should be err", result);
        match result {
            Err(e) => match e {
                Error::ParseError(_) => (),
                e => panic!("should should be Error::ParseError: {:?}", e),
            },
            Ok(s) => panic!("should should be Error::ParseError: {}", s),
        }
    }

    #[test]
    fn parse_semicolon_separated() {
        let result = Production::from_str("<base> ::= \"A\" ; \"C\" ; \"G\" ; \"T\"");
        assert!(result.is_err(), "{:?} should be error", result);

        let production = result.unwrap_err();
        match production {
            Error::ParseError(_) => (),
            e => panic!("invalid production should be parsing error: {:?}", e),
        }
    }
}
