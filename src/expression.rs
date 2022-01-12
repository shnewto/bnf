use error::Error;
use parsers;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops;
use std::slice;
use std::str::FromStr;
use term::Term;

/// An Expression is comprised of any number of Terms
#[derive(Deserialize, Serialize, Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Expression {
    terms: Vec<Term>,
}

impl Expression {
    /// Construct a new `Expression`
    pub fn new() -> Expression {
        Expression { terms: vec![] }
    }

    /// Construct an `Expression` from `Term`s
    pub fn from_parts(v: Vec<Term>) -> Expression {
        Expression { terms: v }
    }

    /// Add `Term` to `Expression`
    pub fn add_term(&mut self, term: Term) {
        self.terms.push(term)
    }

    /// Remove `Term` from `Expression`
    ///
    /// If interested if `Term` was removed, then inspect the returned `Option`.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate bnf;
    /// use bnf::{Expression, Term};
    ///
    /// fn main() {
    ///     let mut expression = Expression::from_parts(vec![]);
    ///     let to_remove = Term::Terminal(String::from("a_terminal"));
    ///     let removed = expression.remove_term(&to_remove);
    ///     # let removed_clone = removed.clone();
    ///     match removed {
    ///         Some(term) => println!("removed {}", term),
    ///         None => println!("term was not in expression, so could not be removed"),
    ///     }
    ///
    ///     # assert_eq!(removed_clone, None);
    /// }
    /// ```
    pub fn remove_term(&mut self, term: &Term) -> Option<Term> {
        if let Some(pos) = self.terms.iter().position(|x| *x == *term) {
            Some(self.terms.remove(pos))
        } else {
            None
        }
    }

    /// Get iterator of `Term`s within `Expression`
    pub fn terms_iter(&self) -> Iter {
        Iter {
            iterator: self.terms.iter(),
        }
    }

    /// Get mutable iterator of `Term`s within `Expression`
    pub fn terms_iter_mut(&mut self) -> IterMut {
        IterMut {
            iterator: self.terms.iter_mut(),
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let display = self
            .terms
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(" ");

        write!(f, "{}", display)
    }
}

impl FromStr for Expression {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parsers::expression_complete(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

impl ops::Add<Expression> for &Expression {
    type Output = Expression;
    fn add(self, rhs: Expression) -> Self::Output {
        let mut new_expression = Expression::new();
        for t in self.terms_iter() {
            new_expression.add_term(t.clone());
        }
        for t in rhs.terms_iter() {
            new_expression.add_term(t.clone());
        }
        new_expression
    }
}

impl ops::Add<Term> for &Expression {
    type Output = Expression;
    fn add(self, rhs: Term) -> Self::Output {
        let mut new_expression = Expression::new();
        for t in self.terms_iter() {
            new_expression.add_term(t.clone());
        }
        new_expression.add_term(rhs);
        new_expression
    }
}

impl ops::Add<Expression> for Expression {
    type Output = Expression;
    fn add(mut self, rhs: Expression) -> Self::Output {
        for t in rhs.terms_iter() {
            self.add_term(t.clone());
        }
        self
    }
}

impl ops::Add<Term> for Expression {
    type Output = Expression;
    fn add(mut self, rhs: Term) -> Self::Output {
        self.add_term(rhs);
        self
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

pub struct IterMut<'a> {
    iterator: slice::IterMut<'a, Term>,
}

impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Term;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}

#[cfg(test)]
mod tests {
    extern crate quickcheck;

    use self::quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
    use super::*;

    impl Arbitrary for Expression {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut terms = Vec::<Term>::arbitrary(g);
            // expressions must always have at least one term
            if terms.is_empty() {
                terms.push(Term::arbitrary(g));
            }
            Expression { terms }
        }
    }

    fn prop_to_string_and_back(expr: Expression) -> TestResult {
        let to_string: String = expr.to_string();
        let from_str: Result<Expression, _> = to_string.parse();
        match from_str {
            Ok(from_expr) => TestResult::from_bool(from_expr == expr),
            _ => TestResult::error(format!("{} to string and back should be safe", expr)),
        }
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new().quickcheck(prop_to_string_and_back as fn(Expression) -> TestResult)
    }

    #[test]
    fn new_expressions() {
        let t1: Term = Term::Terminal(String::from("terminal"));
        let nt1: Term = Term::Nonterminal(String::from("nonterminal"));
        let t2: Term = Term::Terminal(String::from("terminal"));
        let nt2: Term = Term::Nonterminal(String::from("nonterminal"));

        let e1: Expression = Expression::from_parts(vec![nt1, t1]);
        let mut e2: Expression = Expression::new();
        e2.add_term(nt2);
        e2.add_term(t2);

        assert_eq!(e1, e2);
    }

    #[test]
    fn add_term() {
        let mut terms = vec![
            Term::Terminal(String::from("A")),
            Term::Terminal(String::from("C")),
            Term::Terminal(String::from("G")),
        ];

        let mut dna_expression = Expression::from_parts(terms.clone());
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // oops forgot "T"
        let forgotten = Term::Terminal(String::from("T"));
        dna_expression.add_term(forgotten.clone());
        terms.push(forgotten);
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // check all terms are there
        for term in dna_expression.terms_iter() {
            assert!(terms.contains(term), "{} was not in terms", term);
        }
    }

    #[test]
    fn remove_term() {
        let terms = vec![
            Term::Terminal(String::from("A")),
            Term::Terminal(String::from("C")),
            Term::Terminal(String::from("G")),
            Term::Terminal(String::from("T")),
            Term::Terminal(String::from("Z")),
        ];

        let mut dna_expression = Expression::from_parts(terms.clone());
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // oops "Z" isn't a dna base
        let accident = Term::Terminal(String::from("Z"));
        let removed = dna_expression.remove_term(&accident);

        // the removed element should be the accident
        assert_eq!(Some(accident.clone()), removed);
        // number of terms should have decreased
        assert_eq!(dna_expression.terms_iter().count(), terms.len() - 1);
        // the accident should no longer be found in the terms
        assert_eq!(
            dna_expression.terms_iter().find(|&term| *term == accident),
            None
        );
    }

    #[test]
    fn remove_nonexistent_term() {
        let terms = vec![
            Term::Terminal(String::from("A")),
            Term::Terminal(String::from("C")),
            Term::Terminal(String::from("G")),
            Term::Terminal(String::from("T")),
        ];

        let mut dna_expression = Expression::from_parts(terms.clone());
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // oops "Z" isn't a dna base
        let nonexistent = Term::Terminal(String::from("Z"));
        let removed = dna_expression.remove_term(&nonexistent);

        // the nonexistent term should not be found in the terms
        assert_eq!(
            dna_expression
                .terms_iter()
                .find(|&term| *term == nonexistent,),
            None
        );
        // no term should have been removed
        assert_eq!(None, removed);
        // number of terms should not have decreased
        assert_eq!(dna_expression.terms_iter().count(), terms.len());
    }

    #[test]
    fn parse_complete() {
        let expression = Expression::from_parts(vec![
            Term::Nonterminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        assert_eq!(Ok(expression), Expression::from_str("<base> <dna>"));
    }

    #[test]
    fn parse_error() {
        let expression = Expression::from_str("<base> <dna");
        assert!(expression.is_err(), "{:?} should be error", expression);

        let error = expression.unwrap_err();
        match error {
            Error::ParseError(_) => (),
            _ => panic!("{} should be should be error", error),
        }
    }

    #[test]
    fn parse_incomplete() {
        let result = Expression::from_str("");
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
    fn add_operator() {
        let t1 = Term::Terminal(String::from("terminal"));
        let nt1 = Term::Nonterminal(String::from("nonterminal"));
        let t2 = Term::Terminal(String::from("terminal"));
        let nt2 = Term::Nonterminal(String::from("nonterminal"));
        let t3 = Term::Terminal(String::from("terminal"));
        let nt3 = Term::Nonterminal(String::from("nonterminal"));
        let t4 = Term::Terminal(String::from("terminal"));
        let nt4 = Term::Nonterminal(String::from("nonterminal"));
        let t5 = Term::Terminal(String::from("terminal"));
        let nt5 = Term::Nonterminal(String::from("nonterminal"));

        let e1 = Expression::from_parts(vec![nt1, t1]);
        // &expression + expression
        let e2_1 = Expression::from_parts(vec![nt2]);
        let e2_2 = Expression::from_parts(vec![t2]);
        let e2 = &e2_1 + e2_2;
        // &expression + term
        let e3_1 = Expression::from_parts(vec![nt3]);
        let e3 = &e3_1 + t3;
        // expression + expression
        let e4_1 = Expression::from_parts(vec![nt4]);
        let e4_2 = Expression::from_parts(vec![t4]);
        let e4 = e4_1 + e4_2;
        // expression + term
        let e5_1 = Expression::from_parts(vec![nt5]);
        let e5 = e5_1 + t5;

        assert_eq!(e1, e2);
        assert_eq!(e1, e3);
        assert_eq!(e1, e4);
        assert_eq!(e1, e5);
    }
}
