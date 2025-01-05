mod augmented;
mod bnf;

#[cfg(feature = "ABNF")]
pub use augmented::ABNF;
pub use bnf::BNF;

use crate::expression::Expression;
use crate::grammar::Grammar;
use crate::production::Production;
use crate::term::Term;

use nom::{
    branch::alt,
    bytes::complete::{take_till, take_until},
    character::complete::{self, multispace0},
    combinator::{all_consuming, complete, eof, not, peek, recognize},
    error::VerboseError,
    multi::{many0, many1},
    sequence::{delimited, preceded, terminated},
    IResult,
};

pub trait Format {
    fn prod_lhs(input: &str) -> IResult<&str, Term, VerboseError<&str>>;
    fn nonterminal(input: &str) -> IResult<&str, Term, VerboseError<&str>>;
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

pub fn comment(input: &str) -> IResult<&str, &str, VerboseError<&str>> {
    let (input, comment) = preceded(
        complete::char(';'),
        take_till(|c: char| c == '\r' || c == '\n' || c == ';'),
    )(input)?;
    not(complete::char(';'))(input)?;
    Ok((input, comment))
}

pub fn is_format_standard_bnf(input: &str) -> bool {
    match terminated(many0(preceded(multispace0, comment)), multispace0)(input) {
        Ok(tuple) => {
            let (input, _) = tuple;
            complete::char::<&str, VerboseError<&str>>('<')(input).is_ok()
        }
        Err(_) => unreachable!("this pattern should always match"),
    }
}

pub fn term<F: Format>(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    alt((terminal, F::nonterminal))(input)
}

pub fn term_complete<F: Format>(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, t) = all_consuming(term::<F>)(input)?;

    Ok((input, t))
}

pub fn expression_next<F: Format>(input: &str) -> IResult<&str, &str, VerboseError<&str>> {
    let (input, _) = delimited(
        complete::multispace0,
        complete::char('|'),
        complete::multispace0,
    )(input)?;

    complete(expression::<F>)(input)?;

    Ok((input, ""))
}

pub fn expression<F: Format>(input: &str) -> IResult<&str, Expression, VerboseError<&str>> {
    term::<F>(input)?;

    let (input, terms) = many1(complete(term::<F>))(input)?;
    let (input, _) = delimited(
        complete::multispace0,
        alt((
            peek(complete(eof)),
            recognize(peek(complete::char(';'))),
            expression_next::<F>,
            recognize(peek(complete(F::prod_lhs))),
        )),
        complete::multispace0,
    )(input)?;

    Ok((input, Expression::from_parts(terms)))
}

pub fn expression_complete<F: Format>(
    input: &str,
) -> IResult<&str, Expression, VerboseError<&str>> {
    let (input, e) = all_consuming(expression::<F>)(input)?;

    Ok((input, e))
}

pub fn production<F: Format>(input: &str) -> IResult<&str, Production, VerboseError<&str>> {
    let (input, _) = many0(preceded(complete::multispace0, comment))(input)?;
    let (input, lhs) = delimited(complete::multispace0, F::prod_lhs, complete::multispace0)(input)?;
    let (input, rhs) = many1(complete(expression::<F>))(input)?;
    let (input, _) = preceded(
        complete::multispace0,
        alt((
            recognize(peek(complete(eof))),
            comment,
            recognize(peek(complete(F::prod_lhs))),
        )),
    )(input)?;

    Ok((input, Production::from_parts(lhs, rhs)))
}

pub fn production_complete<F: Format>(
    input: &str,
) -> IResult<&str, Production, VerboseError<&str>> {
    let (input, p) = all_consuming(production::<F>)(input)?;

    Ok((input, p))
}

pub fn grammar<F: Format>(input: &str) -> IResult<&str, Grammar, VerboseError<&str>> {
    production::<F>(input)?;
    let (input, prods) = many1(complete(production::<F>))(input.trim_end())?;

    Ok((input, Grammar::from_parts(prods)))
}

pub fn grammar_complete<F: Format>(input: &str) -> IResult<&str, Grammar, VerboseError<&str>> {
    let (input, g) = all_consuming(grammar::<F>)(input)?;

    Ok((input, g))
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn terminal_match() {
        let input = "\"hello world\"";
        let expected = Term::Terminal("hello world".to_string());

        let (_, actual) = terminal(input).unwrap();
        assert_eq!(expected, actual);
    }
}
