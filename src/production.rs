#![allow(clippy::should_implement_trait)]
#![allow(clippy::vec_init_then_push)]

use crate::error::Error;
use crate::expression::Expression;
use crate::parsers;
use crate::term::Term;
use std::fmt;

use nom::Parser;
use nom::combinator::all_consuming;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use std::str::FromStr;

/// A Production is comprised of any number of Expressions
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct Production {
    /// The "left hand side" of the production, i.e. "lhs -> rhs ..."
    pub lhs: Term,
    rhs: Vec<Expression>,
}

impl Production {
    /// Construct a new `Production`
    #[must_use]
    pub const fn new() -> Production {
        Production {
            lhs: Term::Nonterminal(String::new()),
            rhs: vec![],
        }
    }

    /// Construct an `Production` from `Expression`s
    #[must_use]
    pub const fn from_parts(t: Term, e: Vec<Expression>) -> Production {
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
    pub fn rhs_iter(&self) -> impl Iterator<Item = &Expression> {
        self.rhs.iter()
    }

    /// Get mutable iterator of the `Production`'s right hand side `Expression`s
    pub fn rhs_iter_mut(&mut self) -> impl Iterator<Item = &mut Expression> {
        self.rhs.iter_mut()
    }

    /// Get number of right hand side `Expression`s
    #[must_use]
    pub fn len(&self) -> usize {
        self.rhs.len()
    }

    /// If the production is empty of `Expression`s
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rhs.is_empty()
    }

    /// If the production _can_ terminate,
    /// i.e. contains an expression of all terminals or every non-terminal in an
    /// expression exists in the (optional) list of 'terminating rules'
    pub(crate) fn has_terminating_expression(
        &self,
        terminating_rules: Option<&Vec<&Term>>,
    ) -> bool {
        self.rhs.iter().any(|e| e.terminates(terminating_rules))
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
        match all_consuming(parsers::production).parse(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

/// Macro to create a `Production` from a right-hand side definition
/// ```
/// bnf::production!(<S> ::= 'T' <NT> | <NT> "AND");
/// ```
#[macro_export]
macro_rules! production {
    (<$lhs:ident> ::= $($rest:tt)*) => {
        {
            let mut expressions = vec![];
            let mut terms = vec![];
            $crate::production!(@rhs expressions terms $($rest)*);
            expressions.push($crate::Expression::from_parts(terms));
            $crate::Production::from_parts(
                $crate::term!(<$lhs>),
                expressions,
            )
        }
    };
    // munch rhs until empty
    // if terminal, add to expression
    (@rhs $expr:ident $terms:ident $t:literal $($rest:tt)*) => {
        $terms.push($crate::term!($t));
        $crate::production!(@rhs $expr $terms $($rest)*);
    };
    // if nonterminal, add to expression and keep munching
    (@rhs $expr:ident $terms:ident <$nt:ident> $($rest:tt)*) => {
        $terms.push($crate::term!(<$nt>));
        $crate::production!(@rhs $expr $terms $($rest)*);
    };
    // if | add expression to production, and create new expression
    (@rhs $expr:ident $terms:ident | $($rest:tt)*) => {
        $expr.push($crate::Expression::from_parts($terms));
        $terms = vec![];
        $crate::production!(@rhs $expr $terms $($rest)*);
    };
    // base case
    (@rhs $expr:ident $terms:ident) => {};
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
        let from_str = Production::from_str(&to_string)
            .expect("should be able to convert production to string and back");
        TestResult::from_bool(from_str == prop)
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new()
            .tests(1000)
            .r#gen(Gen::new(25usize))
            .quickcheck(prop_to_string_and_back as fn(Production) -> TestResult)
    }

    #[test]
    fn new_productions() {
        let lhs1 = Term::Nonterminal(String::from("STRING A"));
        let rhs1 = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p1 = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2 = Term::Nonterminal(String::from("STRING A"));
        let rhs2 = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let mut p2 = Production::new();
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
                .find(|&expression| *expression == two_more),
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
        let result = Production::from_str("<base> ::= 'A' | 'C' | 'G' |");
        assert!(
            result.is_err(),
            "production result should be error {result:?}"
        );

        let production = result.unwrap_err();
        assert!(
            matches!(production, Error::ParseError(_)),
            "production error should be error: {production:?}"
        );
    }

    #[test]
    fn parse_semicolon_separated() {
        // this should be okay because semicolon is now for comments so stops after A
        let prod = Production::from_str("<base> ::= 'A' ; 'C' ; 'G' ; 'T'").unwrap();
        assert_eq!(prod, crate::production!(<base> ::= 'A'));
    }

    #[test]
    fn parse_incomplete() {
        let result = Production::from_str("");
        assert!(
            matches!(result, Err(Error::ParseError(_))),
            "production result should be error {result:?}"
        );
    }

    #[test]
    fn default_production_empty() {
        let production = Production::default();
        assert!(production.is_empty());
    }

    #[test]
    fn production_len() {
        let production: Production = "<dna> ::= <base> | <dna> <base>".parse().unwrap();
        assert_eq!(production.len(), 2);
    }

    #[test]
    fn format_production() {
        let production: Production = "<dna> ::= <base> | <dna> <base>".parse().unwrap();
        let format = format!("{production}");
        assert_eq!(format, "<dna> ::= <base> | <dna> <base>");
    }

    #[test]
    fn iter_production() {
        let production: Production = "<dna> ::= <base>".parse().unwrap();
        let expressions = production.rhs_iter().cloned().collect::<Vec<_>>();
        assert_eq!(expressions, vec!["<base>".parse().unwrap()]);
    }

    #[test]
    fn iter_mut_production() {
        let mut production: Production = "<dna> ::= <base>".parse().unwrap();
        let new_expr: Expression = "<x> <y> <z>".parse().unwrap();

        for expr in production.rhs_iter_mut() {
            *expr = new_expr.clone();
        }

        assert_eq!(production.rhs_iter().next().unwrap(), &new_expr);
    }

    #[test]
    fn does_have_terminating_expression() {
        let mut production: Production = "<S> ::= 'T'".parse().unwrap();
        assert!(production.has_terminating_expression(None));

        production = "<S> ::= 'T' | <NT>".parse().unwrap();
        assert!(production.has_terminating_expression(None));

        production = "<S> ::= <NT> | 'T'".parse().unwrap();
        assert!(production.has_terminating_expression(None));

        production = "<S> ::= <NT1> | 'T' | <NT2>".parse().unwrap();
        assert!(production.has_terminating_expression(None));

        production = "<S> ::= 'T1' | <NT> | 'T2'".parse().unwrap();
        assert!(production.has_terminating_expression(None));

        production = "<S> ::= <NT1> <NT2> | <NT3> | <NT4>".parse().unwrap();
        assert!(production.has_terminating_expression(Some(&vec![
            &Term::from_str("<NT1>").unwrap(),
            &Term::from_str("<NT2>").unwrap(),
            &Term::from_str("<NTa>").unwrap(),
            &Term::from_str("<NTb>").unwrap(),
        ])));

        production = "<S> ::= <NT1> <NT2> | <NT3> | <NT4>".parse().unwrap();
        assert!(production.has_terminating_expression(Some(&vec![
            &Term::from_str("<NTa>").unwrap(),
            &Term::from_str("<NT4>").unwrap(),
            &Term::from_str("<NTc>").unwrap(),
            &Term::from_str("<NTb>").unwrap(),
        ])));
    }

    #[test]
    fn does_not_have_terminating_expression() {
        let mut production: Production = "<S> ::= <NT>".parse().unwrap();
        assert!(!production.has_terminating_expression(None));

        production = "<S> ::= 'T' <NT>".parse().unwrap();
        assert!(!production.has_terminating_expression(None));

        production = "<S> ::= <NT> 'T'".parse().unwrap();
        assert!(!production.has_terminating_expression(None));

        production = "<S> ::= <NT1> 'T' | <NT2>".parse().unwrap();
        assert!(!production.has_terminating_expression(None));

        production = "<S> ::= <NT1> | <NT> 'T2'".parse().unwrap();
        assert!(!production.has_terminating_expression(None));

        production = "<S> ::= <NT1> <NT2> | <NT3> | <NT4>".parse().unwrap();
        assert!(!production.has_terminating_expression(Some(&vec![
            &Term::from_str("<NT1>").unwrap(),
            &Term::from_str("<NTa>").unwrap(),
            &Term::from_str("<NTb>").unwrap(),
            &Term::from_str("<NTc>").unwrap(),
        ])));

        production = "<S> ::= <NT1> <NT2> | <NT3> | <NT4>".parse().unwrap();
        assert!(!production.has_terminating_expression(Some(&vec![
            &Term::from_str("<NT2>").unwrap(),
            &Term::from_str("<NTa>").unwrap(),
            &Term::from_str("<NTb>").unwrap(),
            &Term::from_str("<NTc>").unwrap(),
        ])));

        production = "<S> ::= <NT1> <NT2> | <NT3> | <NT4>".parse().unwrap();
        assert!(!production.has_terminating_expression(Some(&vec![
            &Term::from_str("<NTa>").unwrap(),
            &Term::from_str("<NTb>").unwrap(),
            &Term::from_str("<NTc>").unwrap(),
            &Term::from_str("<NTd>").unwrap(),
        ])));
    }

    #[test]
    fn macro_builds_todo() {
        let production = crate::production!(<S> ::= 'T' <NT> | <NT> "AND");

        let expected = Production::from_parts(
            Term::Nonterminal(String::from("S")),
            vec![
                Expression::from_parts(vec![
                    Term::Terminal(String::from("T")),
                    Term::Nonterminal(String::from("NT")),
                ]),
                Expression::from_parts(vec![
                    Term::Nonterminal(String::from("NT")),
                    Term::Terminal(String::from("AND")),
                ]),
            ],
        );

        assert_eq!(production, expected);
    }
}
