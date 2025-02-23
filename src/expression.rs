#![allow(clippy::vec_init_then_push)]

use crate::error::Error;
use crate::parsers;
use crate::term::Term;
use std::fmt;
use std::ops;
use std::str::FromStr;

use nom::Parser;
use nom::combinator::all_consuming;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// An Expression is comprised of any number of Terms
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct Expression {
    pub(crate) terms: Vec<Term>,
}

impl Expression {
    /// Construct a new `Expression`
    #[must_use]
    pub const fn new() -> Expression {
        Expression { terms: vec![] }
    }

    /// Construct an `Expression` from `Term`s
    #[must_use]
    pub const fn from_parts(v: Vec<Term>) -> Expression {
        Expression { terms: v }
    }

    /// Add `Term` to `Expression`
    pub fn add_term(&mut self, term: Term) {
        self.terms.push(term);
    }

    /// Remove `Term` from `Expression`
    ///
    /// If interested if `Term` was removed, then inspect the returned `Option`.
    ///
    /// # Example
    ///
    /// ```
    /// use bnf::{Expression, Term};
    ///
    /// let mut expression = Expression::from_parts(vec![]);
    /// let to_remove = Term::Terminal(String::from("a_terminal"));
    /// let removed = expression.remove_term(&to_remove);
    /// # let removed_clone = removed.clone();
    /// match removed {
    ///     Some(term) => println!("removed {}", term),
    ///     None => println!("term was not in expression, so could not be removed"),
    /// }
    ///
    /// # assert_eq!(removed_clone, None);
    /// ```
    pub fn remove_term(&mut self, term: &Term) -> Option<Term> {
        if let Some(pos) = self.terms.iter().position(|x| *x == *term) {
            Some(self.terms.remove(pos))
        } else {
            None
        }
    }

    /// Get iterator of `Term`s within `Expression`
    pub fn terms_iter(&self) -> impl Iterator<Item = &Term> {
        self.terms.iter()
    }

    /// Get mutable iterator of `Term`s within `Expression`
    pub fn terms_iter_mut(&mut self) -> impl Iterator<Item = &mut Term> {
        self.terms.iter_mut()
    }

    /// Determine if this expression terminates or not, i.e contains all terminal elements or every
    /// non-terminal element in the expression exists in the (optional) list of 'terminating rules'
    pub(crate) fn terminates(&self, terminating_rules: Option<&Vec<&Term>>) -> bool {
        if !self.terms.iter().any(|t| matches!(t, Term::Nonterminal(_))) {
            return true;
        }

        let Some(terminating_rules) = terminating_rules else {
            return false;
        };

        let nonterms = self
            .terms_iter()
            .filter(|t| matches!(t, Term::Nonterminal(_)));

        for nt in nonterms {
            if !terminating_rules.contains(&nt) {
                return false;
            }
        }

        true
    }
}

/// Create an expression from a series of terms
/// ```
/// bnf::expression!(<a> "and" <b>);
/// ```
#[macro_export]
macro_rules! expression {
    // rule which matches <ident> followed by token tree
    (<$nt:ident> $($tt:tt)*) => {
        {
            let mut vec = vec![];
            $crate::expression!(vec; <$nt> $($tt)*);
            $crate::Expression::from_parts(vec)
        }
    };
    // rule which matches literal followed by token tree
    ($t:literal $($tt:tt)*) => {
        {
            let mut vec = vec![];
            $crate::expression!(vec; $t $($tt)*);
            $crate::Expression::from_parts(vec)
        }
    };
    // internal rule to handle vector accumulation
    ($vec:ident; <$nt:ident> $($tt:tt)*) => {
        $vec.push($crate::term!(<$nt>));
        $crate::expression!($vec; $($tt)*);
    };
    // internal rule to handle vector accumulation
    ($vec:ident; $t:literal $($tt:tt)*) => {
        $vec.push($crate::term!($t));
        $crate::expression!($vec; $($tt)*);
    };
    // case with vec but no more tt
    ($vec:ident; ) => {};
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let display = self
            .terms
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(" ");

        write!(f, "{display}")
    }
}

impl FromStr for Expression {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match all_consuming(parsers::expression).parse(s) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

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
            _ => TestResult::error(format!("{expr} to string and back should be safe")),
        }
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new().quickcheck(prop_to_string_and_back as fn(Expression) -> TestResult)
    }

    #[test]
    fn new_expressions() {
        let t1 = Term::Terminal(String::from("terminal"));
        let nt1 = Term::Nonterminal(String::from("nonterminal"));
        let t2 = Term::Terminal(String::from("terminal"));
        let nt2 = Term::Nonterminal(String::from("nonterminal"));

        let e1 = Expression::from_parts(vec![nt1, t1]);
        let mut e2 = Expression::new();
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
            assert!(terms.contains(term), "{term} was not in terms");
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
                .find(|&term| *term == nonexistent),
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
        assert!(
            matches!(expression, Err(Error::ParseError(_))),
            "{expression:?} should be error"
        );
    }

    #[test]
    fn parse_incomplete() {
        let result = Expression::from_str("");
        assert!(
            matches!(result, Err(Error::ParseError(_))),
            "{result:?} should be ParseError"
        );
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

    #[test]
    fn iterate_terms() {
        let expression: Expression = "<b> 'A' <b>".parse().unwrap();
        let terms = expression.terms_iter().cloned().collect::<Vec<_>>();
        assert_eq!(terms, expression.terms);
    }

    #[test]
    fn mutate_iterable_terms() {
        let mut expression: Expression = "'END'".parse().unwrap();
        let new_term = Term::Terminal("X".to_string());
        for term in expression.terms_iter_mut() {
            *term = new_term.clone();
        }
        assert_eq!(expression.terms, vec![new_term])
    }

    #[test]
    fn does_not_terminate() {
        let mut expression: Expression;

        expression = "<a> <b> <c>".parse().unwrap();
        assert!(!expression.terminates(None));

        expression = "'a' <b> <c>".parse().unwrap();
        assert!(!expression.terminates(None));

        expression = "<a> 'b' <c>".parse().unwrap();
        assert!(!expression.terminates(None));

        expression = "<a> <b> 'c'".parse().unwrap();
        assert!(!expression.terminates(None));

        expression = "'a' 'b' <c>".parse().unwrap();
        assert!(!expression.terminates(None));

        expression = "'a' <b> 'c'".parse().unwrap();
        assert!(!expression.terminates(None));

        expression = "<a> 'b' 'c'".parse().unwrap();
        assert!(!expression.terminates(None));

        expression = "'a' <b> <c>".parse().unwrap();
        assert!(!expression.terminates(Some(&vec![
            &Term::from_str("<b>").unwrap(),
            &Term::from_str("<1>").unwrap(),
            &Term::from_str("<2>").unwrap(),
        ])));

        expression = "<a> <b> <c>".parse().unwrap();
        assert!(!expression.terminates(Some(&vec![
            &Term::from_str("<c>").unwrap(),
            &Term::from_str("<b>").unwrap(),
            &Term::from_str("<1>").unwrap(),
        ])));
    }

    #[test]
    fn does_terminate() {
        let mut expression: Expression = "'a' 'b' 'c'".parse().unwrap();
        assert!(expression.terminates(None));

        expression = "'a' 'b'".parse().unwrap();
        assert!(expression.terminates(None));

        expression = "'a'".parse().unwrap();
        assert!(expression.terminates(None));

        let mut expression: Expression = "'a' 'b' <c>".parse().unwrap();
        assert!(expression.terminates(Some(&vec![&Term::from_str("<c>").unwrap()])));

        expression = "'a' <b> <c>".parse().unwrap();
        assert!(expression.terminates(Some(&vec![
            &Term::from_str("<c>").unwrap(),
            &Term::from_str("<b>").unwrap(),
        ])));

        expression = "'a' <b> <c>".parse().unwrap();
        assert!(expression.terminates(Some(&vec![
            &Term::from_str("<c>").unwrap(),
            &Term::from_str("<b>").unwrap(),
            &Term::from_str("<1>").unwrap(),
            &Term::from_str("<2>").unwrap(),
        ])));

        expression = "<a> <b> <c>".parse().unwrap();
        assert!(expression.terminates(Some(&vec![
            &Term::from_str("<c>").unwrap(),
            &Term::from_str("<b>").unwrap(),
            &Term::from_str("<1>").unwrap(),
            &Term::from_str("<2>").unwrap(),
            &Term::from_str("<a>").unwrap(),
        ],)));
    }

    #[test]
    fn macro_builds() {
        let expr = expression!(<a> "and" <b>);
        let expected = Expression::from_parts(vec![
            Term::Nonterminal(String::from("a")),
            Term::Terminal(String::from("and")),
            Term::Nonterminal(String::from("b")),
        ]);

        assert_eq!(expr, expected);
    }
}
