//! tools for parsing Extended Backus-Naur Form (EBNF).
// like all good things, this is mostly copied from wikipedia:
// https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form
// full spec that I'm aiming to follow is at https://www.w3.org/TR/REC-xml/#sec-notation
// the ABNF spec is at https://tools.ietf.org/html/rfc5234

#![allow(unused)]

use nom::{
    self,
    branch::alt,
    bytes::complete::{escaped, tag, take_until},
    character::complete,
    combinator::{all_consuming, complete, not, peek, recognize},
    error::{ErrorKind, ParseError, VerboseError},
    multi::{many0, many1},
    sequence::{delimited, preceded, terminated},
    AsChar, IResult, InputIter, InputLength,
};

use grammar::Grammar;
use parsers::terminal; // this much is the same
use production::Production;
use term::Term;

fn space_delimited<I, O, E: ParseError<I>, F>(f: F) -> impl Fn(I) -> IResult<I, O, E>
where
    I: nom::InputTakeAtPosition,
    <I as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
    F: Fn(I) -> IResult<I, O, E>,
{
    let parser = delimited(complete::multispace0, f, complete::multispace0);
    // warning: you can't use delimited(pre, f, post) within the closure, since that's moving the returned parse
    move |input: I| {
        let (input, output) = parser(input)?;
        Ok((input, output))
    }
}

// pub mod symbols {
/// //! [wiki](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form#Table_of_symbols)
/// eats an equals sign
/// ```rust
/// use bnf::ebnf::definition;
/// assert_eq!(definition(" ::= "), Ok(("", "::=")))
/// ```
pub fn definition<'a>(input: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    let (input, definition_symbol) = space_delimited(tag("::="))(input)?;
    Ok((input, definition_symbol))
}

pub fn concatenation() {} // ","
// pub fn termination<'a>(input: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
//     let (input, output) = tag("\n")(input)?;
//     Ok((input, output))
// }
pub fn alternation<'a>(input: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    let (input, output) = tag("|")(input)?;
    Ok((input, output))
}

pub fn optional() {}    // "[" ... "]"
pub fn repetition() {}  // "{" ... "}"
pub fn grouping() {}    // "(" ... ")"
                     // terminal

/// parses a w3c EBNF comment
/// ```rust
/// use bnf::ebnf::comment;
/// assert_eq!(comment(r#"/* foo bar */"#), Ok(("", " foo bar ")));
/// // TODO: assert_eq!(comment(r#"/* foo bar */"#), Ok(("", "foo bar")));
/// // TODO: assert_eq!(comment(r#"/** ... **/"#), Ok(("", "...")));
/// ```
pub fn comment<'a>(input: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    // TODO:
    let (input, output) = delimited(tag(r#"/*"#), take_until(r#"*/"#), tag(r#"*/"#))(input)?;
    Ok((input, output))
}

pub fn exception() {}
// }

/// find nonterminal EBNF symbols
/// ```rust
/// use bnf::Term;
/// use bnf::ebnf::nonterminal;
/// assert_eq!(nonterminal("foo ::="), Ok(("::=", Term::Nonterminal("foo".to_string()))))
/// ```
pub fn nonterminal<'a>(input: &'a str) -> IResult<&'a str, Term, VerboseError<&'a str>> {
    let (input, nt) = complete(space_delimited(complete::alpha1))(input)?;
    Ok((input, Term::Nonterminal(nt.to_string())))
}

pub fn term<'a>(input: &'a str) -> IResult<&'a str, Term, VerboseError<&'a str>> {
    let (input, t) = alt((terminal, nonterminal))(input)?;

    Ok((input, t))
}

/// extract a char code 
/// ```rust
/// use bnf::ebnf::char_code;
/// assert_eq!(char_code("#x84"), Ok(("", 132))); // a newline
/// ```
pub fn char_code<'a>(input: &'a str) -> IResult<&'a str, u32, VerboseError<&'a str>> {
    let (input, output) = preceded(tag("#x"), complete::hex_digit1)(input)?;
    let parsed = u32::from_str_radix(output, 16).unwrap(); 
    Ok((input, parsed))
}

fn a_char<'a>(input: &'a str) -> IResult<&'a str, char, VerboseError<&'a str>>  {
    let (input, output) = complete::none_of("\u{fffe}\u{ffff}")(input)?;
    Ok((input, output))
}


/// recognize a regex character range
/// ```rust
/// use bnf::ebnf::char_set;
/// assert_eq!(char_set("[a-z]"), Ok(("", "[a-z]")));
/// assert_eq!(char_set("[\\]]"), Ok(("", "[\\]]")));
/// ```
pub fn char_set<'a>(input: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
    let parser = recognize(delimited(
        tag("["),
        escaped(complete::none_of("\\]"), '\\', complete::one_of("]")),
        tag("]"),
    ));
    let (input, output) = parser(input)?;
    Ok((input, output))
}

/// 
pub fn char_range(){
    // a_char, Char '-' ( Char - ']' ) 
}

/// 
pub fn production() {}
pub fn grammar() {}
pub fn regex_set() {}
pub fn regex_group() {}
pub fn regex_plus() {}

pub fn to_tree_sitter() {}

#[cfg(test)]
mod tests {
    use super::*;
    fn get_w3c_corpus<'a>() -> &'static str {
        "/* extracted from https://bottlecaps.de/rr/ui on Sun Nov 10, 2019, 13:32 (UTC-05)*/
Grammar  ::= Production*
Production ::= NCName '::=' ( Choice | Link )
NCName   ::= [http://www.w3.org/TR/xml-names/#NT-NCName]
Choice   ::= SequenceOrDifference ( '|' SequenceOrDifference )*
SequenceOrDifference
         ::= (Item ( '-' Item | Item* ))?
Item     ::= Primary ( '?' | '*' | '+' )?
Primary  ::= NCName | StringLiteral | CharCode | CharClass | '(' Choice ')'
StringLiteral
         ::= '\"' [^\"]* '\"' | \"'\" [^']* \"'\"
          /* ws: explicit */
CharCode ::= '#x' [0-9a-fA-F]+
          /* ws: explicit */
CharClass
         ::= '[' '^'? ( Char | CharCode | CharRange | CharCodeRange )+ ']'
          /* ws: explicit */
Char     ::= [http://www.w3.org/TR/xml#NT-Char]
CharRange
         ::= Char '-' ( Char - ']' )
          /* ws: explicit */
CharCodeRange
         ::= CharCode '-' CharCode
          /* ws: explicit */
Link     ::= '[' URL ']'
URL      ::= [^#x5D:/?#]+ '://' [^#x5D#]+ ('#' NCName)?
          /* ws: explicit */
Whitespace
         ::= S | Comment
S        ::= #x9 | #xA | #xD | #x20
Comment  ::= '/*' ( [^*] | '*'+ [^*/] )* '*'* '*/'
          /* ws: explicit */"
    }
    #[test]
    fn check_nonterm() {
        assert_eq!(
            nonterminal("foo ::="),
            Ok(("", Term::Nonterminal("foo".to_string())))
        )
    }
}
