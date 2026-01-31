#![allow(clippy::should_implement_trait)]

use crate::Production;
use crate::error::Error;
use crate::expression::Expression;
use crate::parsers::{self, BNF};
use std::borrow::Cow;
use std::fmt;
use std::ops;
use std::str::FromStr;

use nom::Parser;
use nom::combinator::all_consuming;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A Term can represent a Terminal or Nonterminal node.
///
/// Prefer the constructors [`Term::terminal`] and [`Term::nonterminal`] so you don't have to wrap strings in `Cow` yourself.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum Term<'a> {
    /// A term which cannot be expanded further via productions. Prefer [`Term::terminal`].
    Terminal(Cow<'a, str>),
    /// A term which may be be expanded further via productions. Prefer [`Term::nonterminal`].
    Nonterminal(Cow<'a, str>),
    /// A inline term specified with () or []
    AnonymousNonterminal(Cow<'a, [Expression<'a>]>),
}

impl<'a> Term<'a> {
    /// Create a terminal (literal) from a string.
    ///
    /// Accepts `&str`, `String`, or `Cow<'a, str>`; the `Cow` is chosen automatically
    /// (borrowed for `&str`, owned for `String`).
    ///
    /// # Examples
    ///
    /// ```
    /// use bnf::Term;
    /// use std::borrow::Cow;
    ///
    /// let t1 = Term::terminal("A");
    /// let t2 = Term::terminal(String::from("A"));
    /// let t3 = Term::terminal(Cow::Borrowed("A"));
    /// assert_eq!(t1, t2);
    /// assert_eq!(t1, t3);
    /// ```
    #[must_use]
    pub fn terminal(s: impl Into<Cow<'a, str>>) -> Self {
        Term::Terminal(s.into())
    }

    /// Create a nonterminal from a string.
    ///
    /// Accepts `&str`, `String`, or `Cow<'a, str>`; the `Cow` is chosen automatically
    /// (borrowed for `&str`, owned for `String`).
    ///
    /// # Examples
    ///
    /// ```
    /// use bnf::Term;
    /// use std::borrow::Cow;
    ///
    /// let n1 = Term::nonterminal("dna");
    /// let n2 = Term::nonterminal(String::from("dna"));
    /// let n3 = Term::nonterminal(Cow::Borrowed("dna"));
    /// assert_eq!(n1, n2);
    /// assert_eq!(n1, n3);
    /// ```
    #[must_use]
    pub fn nonterminal(s: impl Into<Cow<'a, str>>) -> Self {
        Term::Nonterminal(s.into())
    }

    /// Create a terminal from a static string in `const` context.
    /// Use this (or the [`term_const!`][macro@crate::term_const!] macro) when building a const grammar.
    #[must_use]
    pub const fn terminal_const(s: &'static str) -> Term<'static> {
        Term::Terminal(Cow::Borrowed(s))
    }

    /// Create a nonterminal from a static string in `const` context.
    /// Use this (or the [`term_const!`][macro@crate::term_const!] macro) when building a const grammar.
    #[must_use]
    pub const fn nonterminal_const(s: &'static str) -> Term<'static> {
        Term::Nonterminal(Cow::Borrowed(s))
    }
}

/// Creates a Terminal if the input is a string literal or a Nonterminal if the input is inside angle brackets.
/// Identifier forms use borrowed strings (no allocation); literal form uses owned so both `"A"` and `'A'` work.
/// ```
/// bnf::term!("terminal");
/// bnf::term!(<nonterminal>);
/// ```
#[macro_export]
macro_rules! term {
    (<$ident:ident>) => {
        $crate::Term::nonterminal_const(stringify!($ident))
    };
    ($ident:ident) => {
        $crate::Term::terminal_const(stringify!($ident))
    };
    // string or char literal (BNF uses 'A'); owned so 'A' (char) works
    ($ident:literal) => {
        $crate::Term::Terminal(std::borrow::Cow::Owned($ident.to_string()))
    };
}

/// Creates a `Term` in `const`/`static` context using borrowed strings (no allocation).
/// Use this when building a const grammar with [`Grammar::from_borrowed`](crate::Grammar::from_borrowed).
///
/// # Examples
///
/// ```
/// use bnf::{Grammar, Production, Expression};
///
/// // Use `static` for grammar data; build arrays by constructing inline (no moving from statics).
/// static DNA_BASE_TERMS: [bnf::Term<'static>; 1] = [bnf::term_const!(<base>)];
/// static DNA_RECUR_TERMS: [bnf::Term<'static>; 2] = [
///     bnf::term_const!(<base>),
///     bnf::term_const!(<dna>),
/// ];
/// static RHS_DNA: [Expression<'static>; 2] = [
///     Expression::from_borrowed(&DNA_BASE_TERMS),
///     Expression::from_borrowed(&DNA_RECUR_TERMS),
/// ];
///
/// static BASE_A: [bnf::Term<'static>; 1] = [bnf::term_const!("A")];
/// static BASE_C: [bnf::Term<'static>; 1] = [bnf::term_const!("C")];
/// static BASE_G: [bnf::Term<'static>; 1] = [bnf::term_const!("G")];
/// static BASE_T: [bnf::Term<'static>; 1] = [bnf::term_const!("T")];
/// static RHS_BASE: [Expression<'static>; 4] = [
///     Expression::from_borrowed(&BASE_A),
///     Expression::from_borrowed(&BASE_C),
///     Expression::from_borrowed(&BASE_G),
///     Expression::from_borrowed(&BASE_T),
/// ];
///
/// static DNA_PRODS: [Production<'static>; 2] = [
///     Production::from_borrowed_rhs(bnf::term_const!(<dna>), &RHS_DNA),
///     Production::from_borrowed_rhs(bnf::term_const!(<base>), &RHS_BASE),
/// ];
/// static DNA_GRAMMAR: Grammar = Grammar::from_borrowed(&DNA_PRODS);
///
/// # fn main() {
/// let parser = DNA_GRAMMAR.build_parser().unwrap();
/// let trees: Vec<_> = parser.parse_input("GATTACA").collect();
/// assert!(!trees.is_empty());
/// # }
/// ```
#[macro_export]
macro_rules! term_const {
    (<$ident:ident>) => {
        $crate::Term::nonterminal_const(stringify!($ident))
    };
    ($lit:literal) => {
        $crate::Term::terminal_const($lit)
    };
}

impl FromStr for Term<'static> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match all_consuming(parsers::term::<BNF>).parse(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

impl<'a> ops::Add<Term<'a>> for Term<'a> {
    type Output = Expression<'a>;

    fn add(self, rhs: Self) -> Self::Output {
        Expression::from_parts(vec![self, rhs])
    }
}

impl<'a> ops::Add<Expression<'a>> for Term<'a> {
    type Output = Expression<'a>;
    fn add(self, mut rhs: Expression<'a>) -> Self::Output {
        rhs.add_term(self);
        rhs
    }
}

impl<'a> ops::Add<&Expression<'a>> for Term<'a> {
    type Output = Expression<'a>;
    fn add(self, rhs: &Expression<'a>) -> Self::Output {
        let mut new = Expression::new();
        for t in rhs.terms_iter() {
            new.add_term(t.clone());
        }
        new.add_term(self);
        new
    }
}

impl<'a> fmt::Display for Term<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Terminal(s) => {
                let s = s.as_ref();
                if s.contains('\'') {
                    write!(f, "\"{s}\"")
                } else {
                    write!(f, "'{s}'")
                }
            }
            Term::Nonterminal(s) => write!(f, "<{}>", s.as_ref()),
            Term::AnonymousNonterminal(exprs) => write!(
                f,
                "{}",
                Production::from_parts(
                    Term::Nonterminal(Cow::Owned("anon-nonterminal".to_owned())),
                    exprs.to_vec()
                )
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    impl Arbitrary for Term<'static> {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut term = String::arbitrary(g);
            if bool::arbitrary(g) {
                term = term.chars().filter(|&c| c != '>').collect();
                Term::Nonterminal(Cow::Owned(term))
            } else {
                if term.contains('"') {
                    term = term.chars().filter(|&c| c != '\'').collect();
                } else if term.contains('\'') {
                    term = term.chars().filter(|&c| c != '"').collect();
                }
                Term::Terminal(Cow::Owned(term))
            }
        }
    }

    fn prop_to_string_and_back(term: Term<'static>) -> TestResult {
        let to_string = term.to_string();
        let from_str = Term::from_str(&to_string);
        match from_str {
            Ok(from_term) => TestResult::from_bool(from_term == term),
            _ => TestResult::error(format!("{term} to string and back should be safe")),
        }
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new().quickcheck(prop_to_string_and_back as fn(Term<'static>) -> TestResult)
    }

    #[test]
    fn parse_complete() {
        assert_eq!(
            Ok(Term::Nonterminal(Cow::Owned(String::from("dna")))),
            Term::from_str("<dna>")
        );
    }

    #[test]
    fn parse_error() {
        let incomplete = Term::from_str("<dna");
        assert!(incomplete.is_err());

        let error = incomplete.unwrap_err();
        assert!(matches!(error, Error::ParseError(s) if s.starts_with("Parsing error: ")));
    }

    #[test]
    fn parse_incomplete() {
        let result = Term::from_str("");
        assert!(matches!(result, Err(Error::ParseError(_))));
    }

    #[test]
    fn anonymous_nonterminal_display() {
        let expr1 = Expression::from_parts(vec![crate::term!("a")]);
        let expr2 = Expression::from_parts(vec![crate::term!("b")]);
        let anon = Term::AnonymousNonterminal(Cow::Owned(vec![expr1, expr2]));
        let display = format!("{}", anon);
        // Should format as a production with "anon-nonterminal" as LHS
        assert!(display.contains("anon-nonterminal"));
        assert!(display.contains("a") || display.contains("b"));
    }

    #[test]
    fn parse_error_display() {
        let incomplete = Term::from_str("<dna");
        assert!(incomplete.is_err());

        let error = incomplete.unwrap_err().to_string();
        assert!(!error.is_empty());
    }

    #[test]
    fn parse_whitespace_nonterm() {
        let some_space = String::from(" some space ");
        assert_eq!(
            Ok(Term::Nonterminal(Cow::Owned(some_space.clone()))),
            Term::from_str(&format!("<{some_space}>"))
        );
    }

    #[test]
    fn parse_whitespace_term() {
        let some_space = String::from(" some space ");
        assert_eq!(
            Ok(Term::Terminal(Cow::Owned(some_space.clone()))),
            Term::from_str(&format!("\"{some_space}\""))
        );
    }

    #[test]
    fn parse_quote_term() {
        let quote_term = Term::from_str("'\"'");
        assert_eq!(
            Ok(Term::Terminal(Cow::Owned(String::from("\"")))),
            quote_term
        );
    }

    #[test]
    fn parse_single_quote_term() {
        let quote_term = Term::from_str("\"'\"");
        assert_eq!(
            Ok(Term::Terminal(Cow::Owned(String::from("'")))),
            quote_term
        );
    }

    #[test]
    fn quote_term_to_string_and_back() {
        let quote = crate::term!("\"");
        let to_string = quote.to_string();
        let from_string = Term::from_str(&to_string);
        assert_eq!(Ok(crate::term!("\"")), from_string);
    }

    #[test]
    fn add_operator() {
        let t1 = crate::term!("terminal");
        let nt1 = crate::term!(<nonterminal>);
        let t2 = crate::term!("terminal");
        let nt2 = crate::term!(<nonterminal>);
        let t3 = crate::term!("terminal");
        let nt3 = crate::term!(<nonterminal>);
        let t4 = crate::term!("terminal");
        let nt4 = crate::term!(<nonterminal>);

        // term + term
        let e1 = Expression::from_parts(vec![nt1, t1]);
        let e2 = nt2 + t2;
        // term + &expression
        let e3_1 = Expression::from_parts(vec![nt3]);
        let e3 = t3 + &e3_1;
        //term + expression
        let e4_1 = Expression::from_parts(vec![nt4]);
        let e4 = t4 + e4_1;

        // Term get's pushed to the end of expression.
        // functionally identical, but different to eq
        // example:
        // nt3 | Expression::from_parts(vec![t3]) != Expression::from_parts(vec![nt3, t3])

        assert_eq!(e1, e2);
        assert_eq!(e1, e3);
        assert_eq!(e1, e4);
    }

    #[test]
    fn macro_terminal() {
        let terminal = crate::term!("terminal");
        assert_eq!(
            Term::Terminal(Cow::Owned(String::from("terminal"))),
            terminal
        );
    }

    #[test]
    fn macro_nonterminal() {
        let nonterminal = crate::term!(<nonterminal>);
        assert_eq!(Term::Nonterminal(Cow::Borrowed("nonterminal")), nonterminal);
    }
}
