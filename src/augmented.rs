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

    fn construct_nonterminal_tuple() -> (Term, String) {
        let nonterminal_pattern = "nonterminal-pattern";
        let nonterminal_value = "nonterminal-pattern";
        let nonterminal_object = Term::Nonterminal(nonterminal_value.to_string());

        (nonterminal_object, nonterminal_pattern.to_string())
    }

    #[test]
    fn nonterminal_match() {
        let nonterminal_tuple = construct_nonterminal_tuple();
        assert_eq!(
            nonterminal_tuple.0,
            ABNF::nonterminal(nonterminal_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_expression_tuple() -> (Expression, String) {
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = tests::construct_terminal_tuple();
        let expression_pattern = nonterminal_tuple.1 + " " + terminal_tuple.1.as_str();
        let expression_object = Expression::from_parts(vec![nonterminal_tuple.0, terminal_tuple.0]);

        (expression_object, expression_pattern)
    }

    #[test]
    fn expression_match() {
        let expression_tuple = construct_expression_tuple();
        assert_eq!(
            expression_tuple.0,
            expression::<ABNF>(expression_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_production_tuple() -> (Production, String) {
        let expression_tuple = construct_expression_tuple();
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = construct_nonterminal_tuple();
        let production_pattern =
            nonterminal_tuple.1 + " = " + &expression_tuple.1 + " | " + &terminal_tuple.1;
        let production_object = Production::from_parts(
            nonterminal_tuple.0,
            vec![
                expression_tuple.0,
                Expression::from_parts(vec![terminal_tuple.0]),
            ],
        );

        (production_object, production_pattern)
    }

    #[test]
    fn production_match() {
        let production_tuple = construct_production_tuple();
        let parsed = production::<ABNF>(production_tuple.1.as_str());
        assert_eq!(production_tuple.0, parsed.unwrap().1);
    }

    fn construct_grammar_tuple() -> (Grammar, String) {
        let production_tuple = construct_production_tuple();
        let grammar_pattern = production_tuple.1.clone() + " " + &production_tuple.1;
        let grammar_object = Grammar::from_parts(vec![
            construct_production_tuple().0,
            construct_production_tuple().0,
        ]);

        (grammar_object, grammar_pattern)
    }

    #[test]
    fn grammar_match() {
        let grammar_tuple = construct_grammar_tuple();
        assert_eq!(
            grammar_tuple.0,
            grammar::<ABNF>(grammar_tuple.1.as_str()).unwrap().1
        );
    }
}
