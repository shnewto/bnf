use crate::parsers::Format;
use crate::term::Term;

use nom::{
    IResult, Parser,
    bytes::complete::{tag, take_till},
    character::complete::{self, satisfy},
    combinator::{complete, not},
};

use super::whitespace_plus_comments;

#[non_exhaustive]
pub struct ABNF;

impl Format for ABNF {
    fn prod_lhs(input: &str) -> IResult<&str, Term> {
        let (input, nt) = take_till(char::is_whitespace)(input)?;

        let (input, _) = whitespace_plus_comments(input).unwrap();
        let (input, _) = complete::char('=')(input)?;
        let (input, _) = whitespace_plus_comments(input).unwrap();

        Ok((input, Term::Nonterminal(nt.to_string())))
    }

    fn nonterminal(input: &str) -> IResult<&str, Term> {
        satisfy(|c: char| c.is_alphabetic() || c == '_').parse(input)?;
        let (input, nt) = take_till(char::is_whitespace)(input)?;
        let (input, _) = whitespace_plus_comments(input).unwrap();

        //if this is the lefhandside of an expression then prod_lhs() should parse this
        not(complete(tag("="))).parse(input)?;

        Ok((input, Term::Nonterminal(nt.to_string())))
    }
}

#[cfg(test)]
mod tests {
    use super::ABNF;
    use crate::parsers::*;

    use crate::expression::Expression;
    use crate::grammar::Grammar;
    use crate::production::Production;
    use crate::term::Term;

    #[test]
    fn nonterminal_match() {
        let input = "nonterminal-pattern";
        let expected = Term::Nonterminal("nonterminal-pattern".to_string());

        let (_, actual) = ABNF::nonterminal(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn expression_match() {
        let input = r#"nonterminal-pattern "terminal-pattern""#;
        let expected = Expression::from_parts(vec![
            Term::Nonterminal("nonterminal-pattern".to_string()),
            Term::Terminal("terminal-pattern".to_string()),
        ]);

        let (_, actual) = expression::<ABNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn production_match() {
        let input = r#"nonterminal-pattern = nonterminal-pattern "terminal-pattern" | "terminal-pattern";\r\n"#;
        let expected =
            Production::from_parts(Term::Nonterminal("nonterminal-pattern".to_string()), vec![
                Expression::from_parts(vec![
                    Term::Nonterminal("nonterminal-pattern".to_string()),
                    Term::Terminal("terminal-pattern".to_string()),
                ]),
                Expression::from_parts(vec![Term::Terminal("terminal-pattern".to_string())]),
            ]);

        let (_, actual) = production::<ABNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn grammar_match() {
        let input = r#"nonterminal-pattern = nonterminal-pattern "terminal-pattern" | "terminal-pattern";\r\n"#;
        let expected = Grammar::from_parts(vec![Production::from_parts(
            Term::Nonterminal("nonterminal-pattern".to_string()),
            vec![
                Expression::from_parts(vec![
                    Term::Nonterminal("nonterminal-pattern".to_string()),
                    Term::Terminal("terminal-pattern".to_string()),
                ]),
                Expression::from_parts(vec![Term::Terminal("terminal-pattern".to_string())]),
            ],
        )]);

        let (_, actual) = grammar::<ABNF>(input).unwrap();
        assert_eq!(expected, actual);
    }
}
