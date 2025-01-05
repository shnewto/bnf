use super::Format;

use crate::term::Term;

use nom::{
    bytes::complete::{tag, take_until},
    character::complete,
    combinator::{complete, not},
    error::VerboseError,
    sequence::{delimited, preceded, terminated},
    IResult,
};

#[non_exhaustive]
pub struct BNF;

impl Format for BNF {
    fn prod_lhs(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
        let (input, nt) =
            delimited(complete::char('<'), take_until(">"), complete::char('>'))(input)?;

        let (input, _) = preceded(complete::multispace0, tag("::="))(input)?;

        Ok((input, Term::Nonterminal(nt.to_string())))
    }

    fn nonterminal(input: &str) -> IResult<&str, Term, VerboseError<&str>> {
        let (input, nt) = complete(delimited(
            complete::char('<'),
            take_until(">"),
            terminated(complete::char('>'), complete::multispace0),
        ))(input)?;

        not(complete(tag("::=")))(input)?;

        Ok((input, Term::Nonterminal(nt.to_string())))
    }
}
