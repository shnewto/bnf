use crate::expression::Expression;
use crate::grammar::Grammar;
use crate::production::Production;
use crate::term::Term;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_until},
    character::complete,
    combinator::{all_consuming, complete, eof, not, peek, recognize},
    error::VerboseError,
    multi::many1,
    sequence::{delimited, preceded, terminated},
    IResult,
};

#[derive(Clone)]
pub enum Format {
    BNF,
    ABNF,
}

pub fn prod_lhs(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, nt) = delimited(
        complete::char('<'),
        take_until(">"),
        complete::char('>'),
    )(input)?;

    let (input, _) = preceded(
        complete::multispace0,
        tag("::="),
    )(input)?;

    Ok((input, Term::Nonterminal(nt.to_string())))
}

pub fn terminal(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, t) = alt((
        delimited(
            complete::char('"'),
            take_until("\""),
            terminated(complete::char('"'), complete::multispace0),
        ),
        delimited(
            complete::char('\''),
            take_until("'"),
            terminated(complete::char('\''), complete::multispace0),
        ),
    ))(input)?;

    Ok((input, Term::Terminal(t.to_string())))
}

pub fn nonterminal(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, nt) = complete(delimited(
        complete::char('<'),
        take_until(">"),
        terminated(complete::char('>'), complete::multispace0),
    ))(input)?;

    not(complete(tag("::=")))(input)?;

    Ok((input, Term::Nonterminal(nt.to_string())))
}

pub fn term(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, t) = alt((terminal, nonterminal))(input)?;
    Ok((input, t))
}

pub fn term_complete(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, t) = all_consuming(term)(input)?;

    Ok((input, t))
}

pub fn expression_next(input: &str) -> IResult<&str, &str, VerboseError<&str>> {
    let (input, _) = delimited(
        complete::multispace0,
        complete::char('|'), 
        complete::multispace0,
    )(input)?;

    peek(complete(expression))(input)?;

    Ok((input, ""))
}

pub fn expression(input: &str) -> IResult<&str, Expression, VerboseError<&str>> {
    let (input, _) = peek(term)(input)?;

    let (input, terms) = many1(complete(term))(input)?;
    let (input, _) = delimited(
        complete::multispace0,
        alt((
            peek(complete(eof)),
            recognize(peek(complete::char(';'))),
            expression_next,
            recognize(peek(complete(prod_lhs))),
        )),
        complete::multispace0,
    )(input)?;

    Ok((input, Expression::from_parts(terms)))
}

pub fn expression_complete(input: &str) -> IResult<&str, Expression, VerboseError<&str>> {
    let (input, e) = all_consuming(expression)(input)?;

    Ok((input, e))
}

pub fn production(input: &str) -> IResult<&str, Production, VerboseError<&str>> {
    let (input, lhs) = delimited(
        complete::multispace0,
        prod_lhs,
        complete::multispace0,
    )(input)?;
    let (input, rhs) = many1(complete(expression))(input)?;
    let (input, _) = preceded(
        complete::multispace0,
        alt((
            recognize(peek(complete(eof))),
            tag(";"),
            recognize(peek(complete(prod_lhs))),
        )),
    )(input)?;

    Ok((input, Production::from_parts(lhs, rhs)))
}

pub fn production_complete(input: &str) -> IResult<&str, Production, VerboseError<&str>> {
    let (input, p) = all_consuming(production)(input)?;

    Ok((input, p))
}

pub fn grammar(input: &str) -> IResult<&str, Grammar, VerboseError<&str>> {
    let (input, _) = peek(production)(input)?;
    let (input, prods) = many1(complete(production))(input.trim_end())?;

    Ok((input, Grammar::from_parts(prods)))
}

pub fn grammar_complete(input: &str) -> IResult<&str, Grammar, VerboseError<&str>> {
    let (input, g) = all_consuming(grammar)(input)?;

    Ok((input, g))
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn construct_terminal_tuple() -> (Term, String) {
        let terminal_pattern = "\"terminal pattern\"";
        let terminal_value = "terminal pattern";
        let terminal_object = Term::Terminal(terminal_value.to_string());

        (terminal_object, terminal_pattern.to_string())
    }

    #[test]
    fn terminal_match() {
        let terminal_tuple = construct_terminal_tuple();
        assert_eq!(
            terminal_tuple.0,
            terminal(terminal_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_nonterminal_tuple() -> (Term, String) {
        let nonterminal_pattern = "<nonterminal-pattern>";
        let nonterminal_value = "nonterminal-pattern";
        let nonterminal_object = Term::Nonterminal(nonterminal_value.to_string());

        (nonterminal_object, nonterminal_pattern.to_string())
    }

    #[test]
    fn nonterminal_match() {
        let nonterminal_tuple = construct_nonterminal_tuple();
        assert_eq!(
            nonterminal_tuple.0,
            nonterminal(nonterminal_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_expression_tuple() -> (Expression, String) {
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = construct_terminal_tuple();
        let expression_pattern = nonterminal_tuple.1 + terminal_tuple.1.as_str();
        let expression_object = Expression::from_parts(vec![nonterminal_tuple.0, terminal_tuple.0]);

        (expression_object, expression_pattern)
    }

    #[test]
    fn expression_match() {
        let expression_tuple = construct_expression_tuple();
        assert_eq!(
            expression_tuple.0,
            expression(expression_tuple.1.as_str()).unwrap().1
        );
    }

    fn construct_production_tuple() -> (Production, String) {
        let expression_tuple = construct_expression_tuple();
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = construct_nonterminal_tuple();
        let production_pattern =
            nonterminal_tuple.1 + "::=" + &expression_tuple.1 + "|" + &terminal_tuple.1 + ";";
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
        let parsed = production(production_tuple.1.as_str());
        assert_eq!(production_tuple.0, parsed.unwrap().1);
    }

    fn construct_grammar_tuple() -> (Grammar, String) {
        let production_tuple = construct_production_tuple();
        let grammar_pattern = production_tuple.1.clone() + &production_tuple.1;
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
            grammar(grammar_tuple.1.as_str()).unwrap().1
        );
    }
}
