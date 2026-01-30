mod augmented;
mod bnf;

mod nom_xt;

#[cfg(feature = "ABNF")]
pub use augmented::ABNF;
pub use bnf::BNF;

use crate::expression::Expression;
use crate::grammar::Grammar;
use crate::production::Production;
use crate::term::Term;
use std::collections::HashSet;

use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::{tag, take_till, take_until},
    character::complete::{self, satisfy},
    combinator::{all_consuming, eof, not, opt, peek, recognize},
    multi::many1,
    sequence::{delimited, preceded, terminated},
};
use nom_xt::xt_list_with_separator;

/// Internal AST representation used while parsing grammar text.
///
/// This layer supports extended grammar syntax (parenthesized groups, optionals,
/// etc.) and is later normalized into the public `Grammar` / `Term` types.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ParsedTerm {
    Terminal(String),
    Nonterminal(String),
    /// A parenthesized group like `(A / B)`
    Group(Vec<ParsedExpression>),
    /// An optional group like `[A / B]`
    Optional(Vec<ParsedExpression>),
}

/// A sequence of `ParsedTerm`s.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct ParsedExpression {
    pub(crate) terms: Vec<ParsedTerm>,
}

impl ParsedExpression {
    pub(crate) const fn new(terms: Vec<ParsedTerm>) -> Self {
        Self { terms }
    }
}

/// A production in the parsed grammar, before normalization.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct ParsedProduction {
    pub(crate) lhs: String,
    pub(crate) rhs: Vec<ParsedExpression>,
}

impl ParsedProduction {
    pub(crate) const fn new(lhs: String, rhs: Vec<ParsedExpression>) -> Self {
        Self { lhs, rhs }
    }
}

/// A full grammar in parsed form, prior to normalization.
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct ParsedGrammar {
    pub(crate) productions: Vec<ParsedProduction>,
}

impl ParsedGrammar {
    pub(crate) const fn new(productions: Vec<ParsedProduction>) -> Self {
        Self { productions }
    }
}

pub trait Format {
    fn nonterminal_delimiter() -> Option<(char, char)>;
    fn production_separator() -> &'static str;
    fn alternative_separator() -> char;
    /// If `Some(c)`, production boundaries can be detected by this character after whitespace
    /// (e.g. BNF uses `'<'`), avoiding a full `prod_lhs` parse as lookahead.
    fn production_start_char() -> Option<char> {
        None
    }
}

#[inline(always)]
fn nonterminal<F: Format>(input: &str) -> IResult<&str, Term> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "nonterminal").entered();
    let (input, nt) = match F::nonterminal_delimiter() {
        Some((start, end)) => delimited(
            complete::char(start),
            take_till(|c: char| c == end),
            complete::char(end),
        )
        .parse(input)?,
        None => {
            satisfy(|c: char| c.is_alphabetic()).parse(input)?;
            take_till(|c: char| c.is_whitespace() || c == ')' || c == ']').parse(input)?
        }
    };

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::Nonterminal(nt.to_string())))
}

#[inline(always)]
fn prod_lhs<F: Format>(input: &str) -> IResult<&str, Term> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "prod_lhs").entered();
    let (input, nt) = nonterminal::<F>(input)?;

    let (input, _) = tag(F::production_separator()).parse(input)?;
    //https://www.rfc-editor.org/rfc/rfc5234.html#section-3.3
    let (input, _) = opt(complete::char(F::alternative_separator())).parse(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, nt))
}

#[inline(always)]
fn prod_rhs<F: Format>(input: &str) -> IResult<&str, Vec<Expression>> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "prod_rhs").entered();
    xt_list_with_separator(expression::<F>, expression_next::<F>).parse(input)
}

#[inline(always)]
pub fn terminal(input: &str) -> IResult<&str, Term> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "terminal").entered();
    let (input, t) = alt((
        delimited(complete::char('"'), take_until("\""), complete::char('"')),
        delimited(complete::char('\''), take_until("'"), complete::char('\'')),
    ))
    .parse(input)?;

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, Term::Terminal(t.to_string())))
}

/// Skips whitespace and ;-comments in one pass. Never fails.
#[inline(always)]
pub fn whitespace_plus_comments(mut input: &str) -> IResult<&str, char> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "whitespace_plus_comments").entered();
    loop {
        let rest = input.trim_start_matches(|c: char| c.is_whitespace());
        if rest.len() == input.len() {
            if rest.starts_with(';') {
                let after_semicolon = &rest[1..];
                if let Some(pos) = after_semicolon.find(|c: char| c == '\r' || c == '\n') {
                    input = &after_semicolon[pos..];
                } else {
                    return Ok(("", '\0'));
                }
            } else {
                return Ok((input, '\0'));
            }
        } else {
            input = rest;
        }
    }
}

pub fn is_format_standard_bnf(input: &str) -> bool {
    let (input, _) = whitespace_plus_comments(input).unwrap();
    complete::char::<&str, nom::error::Error<&str>>('<')
        .parse(input)
        .is_ok()
}

#[inline(always)]
pub fn term<F: Format>(input: &str) -> IResult<&str, Term> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "term").entered();
    alt((terminal, nonterminal::<F>)).parse(input)
}

pub fn expression_next<F: Format>(input: &str) -> IResult<&str, &str> {
    let (input, _) = complete::char(F::alternative_separator()).parse(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, ""))
}

#[inline(always)]
pub fn expression<F: Format>(input: &str) -> IResult<&str, Expression> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "expression").entered();
    let (input, terms) =
        many1(terminated(term::<F>, not(tag(F::production_separator())))).parse(input)?;

    Ok((input, Expression::from_parts(terms)))
}

#[inline(always)]
pub fn production<F: Format>(input: &str) -> IResult<&str, Production> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "production").entered();
    let (input, lhs) = prod_lhs::<F>(input)?;
    let (input, rhs) = prod_rhs::<F>(input)?;
    let (input, _) = match F::production_start_char() {
        Some(start_char) => alt((
            recognize(peek(eof)),
            recognize(peek(preceded(whitespace_plus_comments, complete::char(start_char)))),
        ))
        .parse(input)?,
        None => alt((recognize(peek(eof)), recognize(peek(prod_lhs::<F>)))).parse(input)?,
    };

    Ok((input, Production::from_parts(lhs, rhs)))
}

/// Returns true if the grammar text contains `(` or `[` outside of string literals,
/// i.e. it uses extended syntax (groups or optionals). Used to choose the fast parse path.
pub(crate) fn grammar_has_extended_syntax(input: &str) -> bool {
    if !input.contains('(') && !input.contains('[') {
        return false;
    }
    let mut in_double = false;
    let mut in_single = false;
    for c in input.chars() {
        if in_double {
            if c == '"' {
                in_double = false;
            }
            continue;
        }
        if in_single {
            if c == '\'' {
                in_single = false;
            }
            continue;
        }
        match c {
            '"' => in_double = true,
            '\'' => in_single = true,
            '(' | '[' => return true,
            _ => {}
        }
    }
    false
}

#[allow(dead_code)] // kept for API compatibility; Grammar parsing uses parsed_grammar_complete + normalize
#[inline(always)]
pub fn grammar<F: Format>(input: &str) -> IResult<&str, Grammar> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "grammar").entered();
    let (input, _) = whitespace_plus_comments(input)?;
    production::<F>(input)?;
    let (input, prods) = many1(production::<F>).parse(input)?;
    Ok((input, Grammar::from_parts(prods)))
}

#[allow(dead_code)] // kept for API compatibility; Grammar parsing uses parsed_grammar_complete + normalize
#[inline(always)]
pub fn grammar_complete<F: Format>(input: &str) -> IResult<&str, Grammar> {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "grammar_complete").entered();
    all_consuming(grammar::<F>).parse(input)
}

// ===== Internal parsed-grammar parsing and normalization =====

fn parsed_nonterminal<F: Format>(input: &str) -> IResult<&str, ParsedTerm> {
    let (input, nt) = match F::nonterminal_delimiter() {
        Some((start, end)) => delimited(
            complete::char(start),
            take_till(|c: char| c == end),
            complete::char(end),
        )
        .parse(input)?,
        None => {
            satisfy(|c: char| c.is_alphabetic()).parse(input)?;
            take_till(|c: char| c.is_whitespace() || c == ')' || c == ']').parse(input)?
        }
    };

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, ParsedTerm::Nonterminal(nt.to_string())))
}

fn parsed_terminal(input: &str) -> IResult<&str, ParsedTerm> {
    let (input, t) = alt((
        delimited(complete::char('"'), take_until("\""), complete::char('"')),
        delimited(complete::char('\''), take_until("'"), complete::char('\'')),
    ))
    .parse(input)?;

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, ParsedTerm::Terminal(t.to_string())))
}

fn parsed_expression_next<F: Format>(input: &str) -> IResult<&str, &str> {
    let (input, _) = complete::char(F::alternative_separator()).parse(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, ""))
}

fn parsed_anonymous_group<F: Format>(input: &str) -> IResult<&str, ParsedTerm> {
    let (input, rhs) = delimited(
        complete::char('('),
        xt_list_with_separator(parsed_expression::<F>, parsed_expression_next::<F>),
        complete::char(')'),
    )
    .parse(input)?;

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, ParsedTerm::Group(rhs)))
}

fn parsed_optional_group<F: Format>(input: &str) -> IResult<&str, ParsedTerm> {
    let (input, rhs) = delimited(
        complete::char('['),
        xt_list_with_separator(parsed_expression::<F>, parsed_expression_next::<F>),
        complete::char(']'),
    )
    .parse(input)?;

    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, ParsedTerm::Optional(rhs)))
}

fn parsed_term<F: Format>(input: &str) -> IResult<&str, ParsedTerm> {
    alt((
        parsed_terminal,
        parsed_nonterminal::<F>,
        parsed_anonymous_group::<F>,
        parsed_optional_group::<F>,
    ))
    .parse(input)
}

fn parsed_expression<F: Format>(input: &str) -> IResult<&str, ParsedExpression> {
    let (input, terms) = many1(terminated(
        parsed_term::<F>,
        not(tag(F::production_separator())),
    ))
    .parse(input)?;

    Ok((input, ParsedExpression::new(terms)))
}

fn parsed_prod_lhs<F: Format>(input: &str) -> IResult<&str, String> {
    let (input, nt) = match F::nonterminal_delimiter() {
        Some((start, end)) => delimited(
            complete::char(start),
            take_till(|c: char| c == end),
            complete::char(end),
        )
        .parse(input)?,
        None => {
            satisfy(|c: char| c.is_alphabetic()).parse(input)?;
            take_till(|c: char| c.is_whitespace() || c == ')' || c == ']').parse(input)?
        }
    };

    let (input, _) = whitespace_plus_comments(input).unwrap();
    let (input, _) = tag(F::production_separator()).parse(input)?;
    //https://www.rfc-editor.org/rfc/rfc5234.html#section-3.3
    let (input, _) = opt(complete::char(F::alternative_separator())).parse(input)?;
    let (input, _) = whitespace_plus_comments(input).unwrap();

    Ok((input, nt.to_string()))
}

fn parsed_prod_rhs<F: Format>(input: &str) -> IResult<&str, Vec<ParsedExpression>> {
    xt_list_with_separator(parsed_expression::<F>, parsed_expression_next::<F>).parse(input)
}

fn parsed_production<F: Format>(input: &str) -> IResult<&str, ParsedProduction> {
    let (input, lhs) = parsed_prod_lhs::<F>(input)?;
    let (input, rhs) = parsed_prod_rhs::<F>(input)?;
    let (input, _) =
        alt((recognize(peek(eof)), recognize(peek(parsed_prod_lhs::<F>)))).parse(input)?;

    Ok((input, ParsedProduction::new(lhs, rhs)))
}

fn parsed_grammar<F: Format>(input: &str) -> IResult<&str, ParsedGrammar> {
    let (input, _) = whitespace_plus_comments(input)?;
    let (input, prods) =
        many1(preceded(whitespace_plus_comments, parsed_production::<F>)).parse(input)?;
    Ok((input, ParsedGrammar::new(prods)))
}

pub(crate) fn parsed_grammar_complete<F: Format>(input: &str) -> IResult<&str, ParsedGrammar> {
    all_consuming(parsed_grammar::<F>).parse(input)
}

/// Normalize a parsed grammar (with `Group` and `Optional`) into a `Grammar` that uses only
/// `Term::Terminal` and `Term::Nonterminal`. Anonymous names (`__anon0`, `__anon1`, …) are chosen
/// so they do not clash with any existing LHS nonterminal (e.g. user-defined `<__anon0>`).
/// Optionals `[A / B]` are lowered to a fresh nonterminal with alternatives `A | B | ''`.
pub(crate) fn normalize_parsed_grammar(parsed: ParsedGrammar) -> Grammar {
    #[cfg(feature = "tracing")]
    let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "normalize_parsed_grammar").entered();
    let mut used_names: HashSet<String> = HashSet::new();
    for prod in &parsed.productions {
        used_names.insert(prod.lhs.clone());
    }

    let mut out_prods: Vec<Production> = Vec::new();
    let mut anon_prods: Vec<Production> = Vec::new();

    /// Pick a fresh name that does not collide with user-defined LHS or other generated names.
    fn fresh_anon_name(used: &mut HashSet<String>, counter: &mut usize) -> String {
        loop {
            let candidate = format!("__anon{}", counter);
            *counter += 1;
            if !used.contains(&candidate) {
                used.insert(candidate.clone());
                return candidate;
            }
        }
    }

    fn lower_expression(
        expr: ParsedExpression,
        used: &mut HashSet<String>,
        counter: &mut usize,
        anon_prods: &mut Vec<Production>,
    ) -> Expression {
        #[cfg(feature = "tracing")]
        let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "lower_expression").entered();
        let terms: Vec<Term> = expr
            .terms
            .into_iter()
            .map(|t| lower_term(t, used, counter, anon_prods))
            .collect();
        Expression::from_parts(terms)
    }

    fn lower_term(
        term: ParsedTerm,
        used: &mut HashSet<String>,
        counter: &mut usize,
        anon_prods: &mut Vec<Production>,
    ) -> Term {
        #[cfg(feature = "tracing")]
        let _span = crate::tracing::span!(crate::tracing::Level::DEBUG, "lower_term").entered();
        match term {
            ParsedTerm::Terminal(t) => Term::Terminal(t),
            ParsedTerm::Nonterminal(nt) => Term::Nonterminal(nt),
            ParsedTerm::Group(exprs) => {
                let name = fresh_anon_name(used, counter);
                let anon_lhs = Term::Nonterminal(name.clone());
                let mut lowered_rhs: Vec<Expression> = exprs
                    .into_iter()
                    .map(|e| lower_expression(e, used, counter, anon_prods))
                    .collect();
                // Defensive: empty group () is treated as epsilon (one alternative '').
                if lowered_rhs.is_empty() {
                    lowered_rhs.push(Expression::from_parts(vec![Term::Terminal("".to_owned())]));
                }
                anon_prods.push(Production::from_parts(anon_lhs.clone(), lowered_rhs));
                anon_lhs
            }
            ParsedTerm::Optional(exprs) => {
                let name = fresh_anon_name(used, counter);
                let anon_lhs = Term::Nonterminal(name.clone());
                let mut lowered_rhs: Vec<Expression> = exprs
                    .into_iter()
                    .map(|e| lower_expression(e, used, counter, anon_prods))
                    .collect();
                // Optionals get one extra alternative that is the empty string; empty [] is just epsilon.
                lowered_rhs.push(Expression::from_parts(vec![Term::Terminal("".to_owned())]));
                anon_prods.push(Production::from_parts(anon_lhs.clone(), lowered_rhs));
                anon_lhs
            }
        }
    }

    let mut counter = 0usize;

    for parsed_prod in parsed.productions {
        let lhs_term = Term::Nonterminal(parsed_prod.lhs.clone());
        let rhs_exprs: Vec<Expression> = parsed_prod
            .rhs
            .into_iter()
            .map(|e| lower_expression(e, &mut used_names, &mut counter, &mut anon_prods))
            .collect();
        out_prods.push(Production::from_parts(lhs_term, rhs_exprs));
    }

    out_prods.extend(anon_prods);
    Grammar::from_parts(out_prods)
}

#[cfg(test)]
#[allow(deprecated)] // Grammar::parse_input and parse_input_starting_with are deprecated in favor of GrammarParser
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
    fn empty_group_and_empty_optional_fail_to_parse() {
        // Empty () and [] require at least one expression inside; grammar parse should fail.
        let empty_group: Result<Grammar, _> = "<s> ::= ()".parse();
        assert!(empty_group.is_err(), "empty group () should fail to parse");
        let empty_optional: Result<Grammar, _> = "<s> ::= []".parse();
        assert!(
            empty_optional.is_err(),
            "empty optional [] should fail to parse"
        );
    }

    #[test]
    fn nested_groups_parse_and_parse_input() {
        let grammar: Grammar = "<s> ::= ((<a> | <b>) | <c>)\n<a> ::= 'a'\n<b> ::= 'b'\n<c> ::= 'c'"
            .parse()
            .unwrap();
        let parser = grammar.build_parser().unwrap();
        for input in ["a", "b", "c"] {
            assert!(
                parser.parse_input(input).next().is_some(),
                "nested group should parse '{input}'"
            );
        }
    }

    #[test]
    fn round_trip_formatting_uses_anon() {
        let grammar: Grammar = "<s> ::= (<a> | <b>) [<c>]\n<a> ::= 'a'\n<b> ::= 'b'\n<c> ::= 'c'"
            .parse()
            .unwrap();
        let formatted = format!("{}", grammar);
        assert!(
            formatted.contains("__anon"),
            "formatted grammar should use __anon* nonterminals, got: {formatted}"
        );
        let reparsed: Grammar = formatted.parse().unwrap();
        assert_eq!(
            grammar, reparsed,
            "re-parsing formatted grammar should yield equal grammar"
        );
    }

    #[test]
    fn abnf_groups_and_optionals_parse_and_parse_input() {
        let grammar: Grammar = "s = ('a' / 'b') ['c']\na = 'a'\nb = 'b'\nc = 'c'"
            .parse()
            .unwrap();
        let parser = grammar.build_parser().unwrap();
        assert!(parser.parse_input("a").next().is_some());
        assert!(parser.parse_input("ac").next().is_some());
        assert!(parser.parse_input("b").next().is_some());
        assert!(parser.parse_input("bc").next().is_some());
        assert!(parser.parse_input("").next().is_none());
    }

    #[test]
    fn single_element_group_and_optional() {
        let grammar: Grammar = "<s> ::= (<a>) [<b>]\n<a> ::= 'a'\n<b> ::= 'b'"
            .parse()
            .unwrap();
        let parser = grammar.build_parser().unwrap();
        assert!(
            parser.parse_input("a").next().is_some(),
            "single-element group (<a>) and optional omitted"
        );
        assert!(
            parser.parse_input("ab").next().is_some(),
            "single-element optional [<b>] present"
        );
        assert!(
            parser.parse_input("").next().is_none(),
            "start requires at least <a>"
        );
    }
}
