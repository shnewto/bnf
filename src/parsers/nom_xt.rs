use nom::error::VerboseError;
use nom::{IResult, Parser};

///like `nom::many1` but it accepts a secend parser as an element separator
pub fn xt_list_with_separator<'a, F, O, D, _DO>(
    mut parser: F,
    mut delimiter: D,
) -> impl FnMut(&'a str) -> IResult<&str, Vec<O>, VerboseError<&str>>
where
    F: Parser<&'a str, O, VerboseError<&'a str>>,
    D: Parser<&'a str, _DO, VerboseError<&'a str>>,
{
    move |mut input: &str| {
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
