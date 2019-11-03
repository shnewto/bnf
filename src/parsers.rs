use expression::Expression;
use grammar::Grammar;
use production::Production;
use term::Term;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_until},
    character::complete,
    combinator::{all_consuming, complete, peek, recognize},
    error::VerboseError,
    multi::many1,
    sequence::{delimited, preceded, terminated},
    IResult,
};

fn prod_lhs<'a>(input: &'a str) -> IResult<&'a str, Term, VerboseError<&'a str>> {
    let (input, _) = delimited(
        complete::char('<'),
        take_until(">"),
        preceded(
            complete::multispace0,
            terminated(complete::char('>'), complete::multispace1),
        ),
    )(input)?;

    let (input, nt) = preceded(
        complete::multispace0,
        terminated(tag("::="), complete::multispace1),
    )(input)?;

    Ok((input, Term::Nonterminal(String::from(nt))))
}

fn terminal<'a>(input: &'a str) -> IResult<&'a str, Term, VerboseError<&'a str>> {
    let (input, t) = alt((
        delimited(
            complete::char('"'),
            take_until("\""),
            preceded(
                complete::multispace0,
                terminated(complete::char('"'), complete::multispace1),
            ),
        ),
        preceded(
            complete::multispace0,
            terminated(tag("::="), complete::multispace1),
        ),
    ))(input)?;

    Ok((input, Term::Nonterminal(String::from(t))))
}

fn nonterminal<'a>(input: &'a str) -> IResult<&'a str, Term, VerboseError<&'a str>> {
    let (input, nt) = complete(delimited(
        complete::char('<'),
        take_until(">"),
        preceded(
            complete::multispace0,
            terminated(complete::char('>'), complete::multispace1),
        ),
    ))(input)?;

    let (input, _) = complete(preceded(
        complete::multispace0,
        terminated(tag("::="), complete::multispace1),
    ))(input)?;

    Ok((input, Term::Nonterminal(String::from(nt))))
}

fn term<'a>(input: &'a str) -> IResult<&'a str, Term, VerboseError<&'a str>> {
    let (input, t) = alt((terminal, nonterminal))(input)?;

    Ok((input, t))
}

fn term_complete<'a>(input: &'a str) -> IResult<&'a str, Term, VerboseError<&'a str>> {
    let (input, t) = all_consuming(term)(input)?;

    Ok((input, t))
}

fn expression_next<'a>(input: &'a str) -> IResult<&'a str, &str, VerboseError<&'a str>> {
    let (input, _) = preceded(
        complete::multispace0,
        terminated(complete::char('|'), complete::multispace1),
    )(input)?;

    let (input, e) = recognize(peek(complete(expression)))(input)?;

    Ok((input, e))
}

fn expression<'a>(input: &'a str) -> IResult<&'a str, Expression, VerboseError<&'a str>> {
    let (input, _) = peek(term)(input)?;

    let (input, terms) = many1(complete(term))(input)?;
    let (input, _) = preceded(
        complete::multispace0,
        terminated(
            alt((
                recognize(peek(complete(complete::char(';')))),
                expression_next,
                recognize(peek(complete(prod_lhs))),
            )),
            complete::multispace1,
        ),
    )(input)?;

    Ok((input, Expression::from_parts(terms)))
}

fn expression_complete<'a>(input: &'a str) -> IResult<&'a str, Expression, VerboseError<&'a str>> {
    let (input, e) = all_consuming(expression)(input)?;

    Ok((input, e))
}

fn production<'a>(input: &'a str) -> IResult<&'a str, Production, VerboseError<&'a str>> {
    let (input, lhs) = preceded(
        complete::multispace0,
        terminated(prod_lhs, complete::multispace1),
    )(input)?;
    let (input, rhs) = many1(complete(expression))(input)?;
    let (input, _) = preceded(
        complete::multispace0,
        terminated(
            alt((tag(";"), recognize(peek(complete(prod_lhs))))),
            complete::multispace1,
        ),
    )(input)?;

    Ok((input, Production::from_parts(lhs, rhs)))
}

fn production_complete<'a>(input: &'a str) -> IResult<&'a str, Production, VerboseError<&'a str>> {
    let (input, p) = all_consuming(production)(input)?;

    Ok((input, p))
}

fn grammar<'a>(input: &'a str) -> IResult<&'a str, Grammar, VerboseError<&'a str>> {
    let (input, _) = peek(production)(input)?;
    let (input, prods) = many1(complete(production))(input)?;

    Ok((input, Grammar::from_parts(prods)))
}

fn grammar_complete<'a>(input: &'a str) -> IResult<&'a str, Grammar, VerboseError<&'a str>> {
    let (input, g) = all_consuming(grammar)(input)?;

    Ok((input, g))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn construct_terminal_tuple() -> (Term, String) {
        let terminal_pattern = "\"terminal pattern\"";
        let terminal_value = "terminal pattern";
        let terminal_object = Term::Terminal(String::from(terminal_value));

        (terminal_object, String::from(terminal_pattern))
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
        let nonterminal_object = Term::Nonterminal(String::from(nonterminal_value));

        (nonterminal_object, String::from(nonterminal_pattern))
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
        let expression_pattern = nonterminal_tuple.1 + &terminal_tuple.1;
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
                expression_tuple.0.clone(),
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
            construct_production_tuple().0.clone(),
            construct_production_tuple().0,
        ]);

        (grammar_object, String::from(grammar_pattern))
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
