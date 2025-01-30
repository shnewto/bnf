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
    combinator::{all_consuming, complete, eof, opt, peek, recognize},
    multi::many1,
    sequence::{delimited, preceded},
    IResult, Parser,
};

pub trait Format {
    fn prod_lhs(input: &str) -> IResult<&str, Term>;
    fn nonterminal(input: &str) -> IResult<&str, Term>;
}

pub fn terminal(input: &str) -> IResult<&str, Term> {
    let (input, t) = alt((
        delimited(complete::char('"'), take_until("\""), complete::char('"')),
        delimited(complete::char('\''), take_until("'"), complete::char('\'')),
    ))
    .parse(input)?;

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::Terminal(t.to_string())))
}

///this should never fail, unwrap it when calling directly please!
pub fn whitespace_plus_comments(mut input: &str) -> IResult<&str, char> {
    let mut old_input = input;
    loop {
        (input, _) = multispace0::<&str, nom::error::Error<&str>>.parse(input)?;
        (input, _) = opt(preceded(
            complete::char(';'),
            take_till(|c: char| c == '\r' || c == '\n'),
        ))
        .parse(input)?;

        if input == old_input {
            break;
        }
        old_input = input
    }
    Ok((input, '\0'))
}

pub fn is_format_standard_bnf(input: &str) -> bool {
    let (input, _) = whitespace_plus_comments(input).unwrap();
    complete::char::<&str, nom::error::Error<&str>>('<')
        .parse(input)
        .is_ok()
}

pub fn term<F: Format>(input: &str) -> IResult<&str, Term> {
    alt((terminal, F::nonterminal)).parse(input)
}

pub fn term_complete<F: Format>(input: &str) -> IResult<&str, Term> {
    all_consuming(term::<F>).parse(input)
}

pub fn expression_next<F: Format>(input: &str) -> IResult<&str, &str> {
    let (input, _) = complete::char('|').parse(input)?;
    let (input, _) = whitespace_plus_comments(input)?;
    complete(expression::<F>).parse(input)?;
    Ok((input, ""))
}

pub fn expression<F: Format>(input: &str) -> IResult<&str, Expression> {
    term::<F>(input)?;
    let (input, terms) = many1(complete(term::<F>)).parse(input)?;
    let (input, _) = alt((
        peek(complete(eof)),
        expression_next::<F>,
        recognize(peek(complete(F::prod_lhs))),
    ))
    .parse(input)?;
    Ok((input, Expression::from_parts(terms)))
}

pub fn expression_complete<F: Format>(input: &str) -> IResult<&str, Expression> {
    all_consuming(expression::<F>).parse(input)
}

pub fn production<F: Format>(input: &str) -> IResult<&str, Production> {
    let (input, lhs) = F::prod_lhs(input)?;
    let (input, rhs) = many1(complete(expression::<F>)).parse(input)?;
    let (input, _) = whitespace_plus_comments(input)?;
    let (input, _) = alt((
        recognize(peek(complete(eof))),
        recognize(peek(complete(F::prod_lhs))),
    ))
    .parse(input)?;
    Ok((input, Production::from_parts(lhs, rhs)))
}

pub fn production_complete<F: Format>(input: &str) -> IResult<&str, Production> {
    all_consuming(production::<F>).parse(input)
}

pub fn grammar<F: Format>(input: &str) -> IResult<&str, Grammar> {
    let (input, _) = whitespace_plus_comments(input)?;
    production::<F>(input)?;
    let (input, prods) = many1(complete(production::<F>)).parse(input)?;
    Ok((input, Grammar::from_parts(prods)))
}

pub fn grammar_complete<F: Format>(input: &str) -> IResult<&str, Grammar> {
    all_consuming(grammar::<F>).parse(input)
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
