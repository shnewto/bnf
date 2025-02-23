use crate::expression::Expression;
use crate::grammar::Grammar;
use crate::production::Production;
use crate::term::Term;

use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::{tag, take_till, take_until},
    character::complete::{self, multispace0, satisfy},
    combinator::{all_consuming, eof, not, opt, peek, recognize},
    error::ParseError,
    multi::many1,
    sequence::{delimited, preceded, terminated},
};

fn nonterminal(input: &str) -> IResult<&str, Term> {
    let (input, nt) = if input.starts_with('<') {
        delimited(
            complete::char('<'),
            take_till(|c: char| c == '>'),
            complete::char('>'),
        )
        .parse(input)?
    } else {
        satisfy(|c: char| c.is_alphabetic()).parse(input)?;
        take_till(|c: char| c.is_whitespace() || c == ')' || c == ']').parse(input)?
    };

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::Nonterminal(nt.to_string())))
}

fn prod_lhs(input: &str) -> IResult<&str, Term> {
    let (input, nt) = nonterminal(input)?;

    let (input, _) = alt((tag("::="), tag("="))).parse(input)?;
    //https://www.rfc-editor.org/rfc/rfc5234.html#section-3.3
    let (input, _) = opt(alt((complete::char('|'), complete::char('/')))).parse(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, nt))
}

fn prod_rhs(input: &str) -> IResult<&str, Vec<Expression>> {
    xt_list_with_separator(expression, expression_next).parse(input)
}

///like `nom::many1` but it accepts a secend parser as an element separator
pub fn xt_list_with_separator<I, F, D, E>(
    mut parser: F,
    mut delimiter: D,
) -> impl Parser<I, Output = Vec<<F as Parser<I>>::Output>, Error = E>
where
    I: Clone + nom::Input + Copy,
    F: Parser<I, Error = E>,
    D: Parser<I, Error = E>,
    E: ParseError<I>,
{
    move |mut input: I| {
        let mut acc = vec![];
        loop {
            match parser.parse(input) {
                Ok((i, o)) => {
                    acc.push(o);
                    input = i;
                    match delimiter.parse(input) {
                        Ok((i, _)) => {
                            input = i;
                            continue;
                        }
                        Err(nom::Err::Error(_)) => break,
                        Err(e) => return Err(e),
                    }
                }
                Err(e) => return Err(e),
            }
        }
        Ok((input, acc))
    }
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

pub fn term(input: &str) -> IResult<&str, Term> {
    alt((
        terminal,
        nonterminal,
        anonymous_nonterminal,
        optional_anonymous_nonterminal,
    ))
    .parse(input)
}

pub fn expression_next(input: &str) -> IResult<&str, &str> {
    let (input, _) = alt((complete::char('|'), complete::char('/'))).parse(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, ""))
}

pub fn expression(input: &str) -> IResult<&str, Expression> {
    let (input, terms) = many1(terminated(term, not(alt((tag("::="), tag("=")))))).parse(input)?;

    Ok((input, Expression::from_parts(terms)))
}

pub fn production(input: &str) -> IResult<&str, Production> {
    let (input, lhs) = prod_lhs(input)?;
    let (input, rhs) = prod_rhs(input)?;
    let (input, _) = alt((recognize(peek(eof)), recognize(peek(prod_lhs)))).parse(input)?;

    Ok((input, Production::from_parts(lhs, rhs)))
}

pub fn anonymous_nonterminal(input: &str) -> IResult<&str, Term> {
    let (input, rhs) =
        delimited(complete::char('('), prod_rhs, complete::char(')')).parse(input)?;

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::AnonymousNonterminal(rhs)))
}

pub fn optional_anonymous_nonterminal(input: &str) -> IResult<&str, Term> {
    let (input, mut rhs) =
        delimited(complete::char('['), prod_rhs, complete::char(']')).parse(input)?;

    rhs.push(Expression::from_parts(vec![Term::Terminal("".to_owned())]));

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::AnonymousNonterminal(rhs)))
}

pub fn grammar(input: &str) -> IResult<&str, Grammar> {
    let (input, _) = whitespace_plus_comments(input)?;
    production(input)?;
    let (input, prods) = many1(production).parse(input)?;
    Ok((input, Grammar::from_parts(prods)))
}

pub fn grammar_complete(input: &str) -> IResult<&str, Grammar> {
    all_consuming(grammar).parse(input)
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
    fn use_anon_nonterminal() {
        let grammar = "s = ('a' / 'b') 'c'";
        let grammar = grammar.parse::<Grammar>().unwrap();
        let inputs = vec!["ac", "bc"];
        for input in inputs {
            assert!(grammar.parse_input(input).next().is_some());
        }
    }

    #[test]
    fn parse_optional_anon_nonterminal() {
        let input = "s = 'c' ['a' / 'b']";
        let expected = "s = 'c' ('a' / 'b' / '')";
        let input = input.parse::<Grammar>().unwrap();
        let twin = expected.parse::<Grammar>().unwrap();
        assert_eq!(input, twin)
    }
    #[test]
    //https://www.rfc-editor.org/rfc/rfc5234.html#section-3.3
    fn parse_incremental_alternatives() {
        let grammar = "s = a / a s
                            a = 'b'
                            a =/ 'c'";
        assert!(grammar.parse::<Grammar>().is_ok());
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
    #[test]
    fn nonterminal_match() {
        let input = "<nonterminal-pattern>";
        let input_aug = "nonterminal-pattern";
        let expected = Term::Nonterminal("nonterminal-pattern".to_string());

        let (_, actual) = nonterminal(input).unwrap();
        let (_, actual_aug) = nonterminal(input_aug).unwrap();
        assert_eq!(expected, actual);
        assert_eq!(expected, actual_aug);
    }
    #[test]
    fn expression_match() {
        let input = r#"<nonterminal-pattern> "terminal-pattern""#;
        let input_aug = r#"nonterminal-pattern "terminal-pattern""#;
        let expected = Expression::from_parts(vec![
            Term::Nonterminal("nonterminal-pattern".to_string()),
            Term::Terminal("terminal-pattern".to_string()),
        ]);

        let (_, actual) = expression(input).unwrap();
        let (_, actual_aug) = expression(input_aug).unwrap();
        assert_eq!(expected, actual);
        assert_eq!(expected, actual_aug);
    }
    #[test]
    fn production_match() {
        let input = r#"<nonterminal-pattern> ::= <nonterminal-pattern> "terminal-pattern" | "terminal-pattern";\r\n"#;
        let input_aug = r#"nonterminal-pattern = nonterminal-pattern "terminal-pattern" / "terminal-pattern";\r\n"#;
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

        let (_, actual) = production(input).unwrap();
        let (_, actual_aug) = production(input_aug).unwrap();
        assert_eq!(expected, actual);
        assert_eq!(expected, actual_aug);
    }
    #[test]
    fn grammar_match() {
        let input = r#"<nonterminal-pattern> ::= <nonterminal-pattern> "terminal-pattern" | "terminal-pattern";\r\n"#;
        let input_aug = r#"nonterminal-pattern = nonterminal-pattern "terminal-pattern" / "terminal-pattern";\r\n"#;
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

        let (_, actual) = grammar(input).unwrap();
        let (_, actual_aug) = grammar(input_aug).unwrap();
        assert_eq!(expected, actual);
        assert_eq!(expected, actual_aug);
    }
}
