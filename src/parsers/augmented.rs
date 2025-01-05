use crate::parsers::Format;
use crate::term::Term;

use nom::{
    bytes::complete::{tag, take, take_till},
    character::complete::{self, satisfy},
    combinator::{complete, not},
    error::VerboseError,
    sequence::{preceded, terminated},
    IResult,
};

#[non_exhaustive]
pub struct ABNF;

impl Format for ABNF {
    fn prod_lhs(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
        let (input, nt) = take_till(char::is_whitespace)(input)?;

        let (input, _) = preceded(complete::multispace0, complete::char('='))(input)?;

        Ok((input, Term::Nonterminal(nt.to_string())))
    }

    fn nonterminal(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
        satisfy(|c: char| c.is_alphanumeric() || c == '_')(input)?;
        let (input, nt) = complete(terminated(
            take_till(char::is_whitespace),
            complete::multispace0,
        ))(input)?;
        take(1_usize)(nt)?;

        not(complete(tag("=")))(input)?;

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
        let expected = Production::from_parts(
            Term::Nonterminal("nonterminal-pattern".to_string()),
            vec![
                Expression::from_parts(vec![
                    Term::Nonterminal("nonterminal-pattern".to_string()),
                    Term::Terminal("terminal-pattern".to_string()),
                ]),
                Expression::from_parts(vec![Term::Terminal("terminal-pattern".to_string())]),
            ],
        );

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
