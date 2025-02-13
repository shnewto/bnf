use super::{whitespace_plus_comments, Format};

use crate::term::Term;

use nom::{
    bytes::complete::{tag, take_until},
    character::complete,
    combinator::{complete, not},
    sequence::delimited,
    IResult, Parser,
};

#[non_exhaustive]
pub struct BNF;

impl Format for BNF {
    fn prod_lhs(input: &str) -> IResult<&str, Term> {
        let (input, nt) =
            delimited(complete::char('<'), take_until(">"), complete::char('>')).parse(input)?;
        let (input, _) = whitespace_plus_comments(input).unwrap();
        let (input, _) = tag("::=").parse(input)?;
        let (input, _) = whitespace_plus_comments(input).unwrap();

        Ok((input, Term::Nonterminal(nt.to_string())))
    }

    fn nonterminal(input: &str) -> IResult<&str, Term> {
        let (input, nt) =
            delimited(complete::char('<'), take_until(">"), complete::char('>')).parse(input)?;
        let (input, _) = whitespace_plus_comments(input).unwrap();
        not(complete(tag("::="))).parse(input)?;
        Ok((input, Term::Nonterminal(nt.to_string())))
    }
}

#[cfg(test)]
mod tests {
    use super::BNF;
    use crate::parsers::*;

    #[test]
    fn nonterminal_match() {
        let input = "<nonterminal-pattern>";
        let expected = Term::Nonterminal("nonterminal-pattern".to_string());

        let (_, actual) = BNF::nonterminal(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn expression_match() {
        let input = r#"<nonterminal-pattern> "terminal-pattern""#;
        let expected = Expression::from_parts(vec![
            Term::Nonterminal("nonterminal-pattern".to_string()),
            Term::Terminal("terminal-pattern".to_string()),
        ]);

        let (_, actual) = expression::<BNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn production_match() {
        let input = r#"<nonterminal-pattern> ::= <nonterminal-pattern> "terminal-pattern" | "terminal-pattern";\r\n"#;
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

        let (_, actual) = production::<BNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn grammar_match() {
        let input = r#"<nonterminal-pattern> ::= <nonterminal-pattern> "terminal-pattern" | "terminal-pattern";\r\n"#;
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

        let (_, actual) = grammar::<BNF>(input).unwrap();
        assert_eq!(expected, actual);
    }
}
