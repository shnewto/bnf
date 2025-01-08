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
    bytes::complete::{tag, take_till, take_until},
    character::complete::{self, multispace0, satisfy},
    combinator::{all_consuming, complete, eof, not, opt, peek, recognize},
    error::VerboseError,
    multi::many1,
    sequence::{delimited, preceded, terminated},
    IResult,
};

///like `nom::many1` but it accepts a secend parser as an element separator
// pub fn xt_list_with_separator()

pub trait Format {
    fn nonterminal_delimiter() -> Option<(char, char)>;
    fn production_separator() -> &'static str;
    fn alternative_separator() -> char;
}

fn nonterminal<F: Format>(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, nt) = match F::nonterminal_delimiter() {
        Some((start, end)) => delimited(
            complete::char(start),
            take_till(|c: char| c == end),
            complete::char(end),
        )(input)?,
        None => {
            satisfy(|c: char| c.is_alphabetic())(input)?;
            take_till(char::is_whitespace)(input)?
        }
    };

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::Nonterminal(nt.to_string())))
}

fn prod_lhs<F: Format>(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, nt) = nonterminal::<F>(input)?;

    let (input, _) = tag(F::production_separator())(input)?;
    //https://www.rfc-editor.org/rfc/rfc5234.html#section-3.3
    let (input, _) = opt(complete::char(F::alternative_separator()))(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, nt))
}

pub fn terminal(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    let (input, t) = alt((
        delimited(complete::char('"'), take_until("\""), complete::char('"')),
        delimited(complete::char('\''), take_until("'"), complete::char('\'')),
    ))(input)?;

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::Terminal(t.to_string())))
}

///this should never fail, unwrap it when calling directly please!
pub fn whitespace_plus_comments(mut input: &str) -> IResult<&str, char, VerboseError<&str>> {
    let mut old_input = input;
    loop {
        (input, _) = multispace0(input)?;
        (input, _) = opt(preceded(
            complete::char(';'),
            take_till(|c: char| c == '\r' || c == '\n'),
        ))(input)?;

        if input == old_input {
            break;
        }
        old_input = input
    }
    Ok((input, '\0'))
}

pub fn is_format_standard_bnf(input: &str) -> bool {
    let (input, _) = whitespace_plus_comments(input).unwrap();
    complete::char::<&str, VerboseError<&str>>('<')(input).is_ok()
}

pub fn term<F: Format>(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
    alt((terminal, nonterminal::<F>))(input)
}

pub fn expression_next<F: Format>(input: &str) -> IResult<&str, &str, VerboseError<&str>> {
    let (input, _) = complete::char(F::alternative_separator())(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    complete(expression::<F>)(input)?;

    Ok((input, ""))
}

pub fn expression<F: Format>(input: &str) -> IResult<&str, Expression, VerboseError<&str>> {
    let (input, terms) = many1(terminated(term::<F>, not(tag(F::production_separator()))))(input)?;
    let (input, _) = alt((
        peek(complete(eof)),
        expression_next::<F>,
        recognize(peek(complete(prod_lhs::<F>))),
    ))(input)?;

    Ok((input, Expression::from_parts(terms)))
}

pub fn production<F: Format>(input: &str) -> IResult<&str, Production, VerboseError<&str>> {
    let (input, lhs) = prod_lhs::<F>(input)?;
    let (input, rhs) = many1(complete(expression::<F>))(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();
    let (input, _) = alt((
        recognize(peek(complete(eof))),
        recognize(peek(complete(prod_lhs::<F>))),
    ))(input)?;

    Ok((input, Production::from_parts(lhs, rhs)))
}

pub fn grammar<F: Format>(input: &str) -> IResult<&str, Grammar, VerboseError<&str>> {
    let (input, _) = whitespace_plus_comments(input).unwrap();
    production::<F>(input)?;
    let (input, prods) = many1(complete(production::<F>))(input)?;

    Ok((input, Grammar::from_parts(prods)))
}

pub fn grammar_complete<F: Format>(input: &str) -> IResult<&str, Grammar, VerboseError<&str>> {
    all_consuming(grammar::<F>)(input)
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

    #[test]
    fn parse_anon_nonterminal() {
        let input = "s = ('a' 'b') / 'c'";
        //15 is the amount of characters left in anon at the start of the (
        let expected = "<s> ::= <15> | 'c'
                        <15> ::= 'a' 'b'";
        let input = input.parse::<Grammar>().unwrap();
        let twin = expected.parse::<Grammar>().unwrap();
        assert_eq!(input, twin)
    }

    #[test]
    fn parse_optional_anon_nonterminal() {
        let input = "s = 'c' ['a' / 'b']";
        let expected = "<s> ::= 'c' <11>
                        <11> ::= 'a' | 'b' | ''";
        let input = input.parse::<Grammar>().unwrap();
        let twin = expected.parse::<Grammar>().unwrap();
        assert_eq!(input, twin)
    }
    #[test]
    //https://www.rfc-editor.org/rfc/rfc5234.html#section-3.3
    fn parse_incremental_alternatives() {
        let input = "s = a / (a s)
                            a = 'b'
                            a =/ 'c'";
        let expected = "<s> ::= <a> | <78>
                                <78> ::= <a> <s>
                                <a> ::= 'b'
                                <a> ::= 'c'";
        let input = input.parse::<Grammar>().unwrap();
        let expected = expected.parse::<Grammar>().unwrap();
        assert_eq!(input, expected);
        // panic!()
    }
    #[test]
    fn use_incremental_alternatives() {
        let input = "s = a / (a s)
                            a = 'b'
                            a =/ 'c'";
        let grammar = input.parse::<Grammar>().unwrap();
        grammar
            .parse_input("bcbccbbcbcbcbbbbbbbbbbbbccc")
            .next()
            .unwrap();
    }
}
