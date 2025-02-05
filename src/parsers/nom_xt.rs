use nom::{error::ParseError, Input, Parser};

///like `nom::many1` but it accepts a secend parser as an element separator
pub fn xt_list_with_separator<I, F, D, E>(
    mut parser: F,
    mut delimiter: D,
) -> impl Parser<I, Output = Vec<<F as Parser<I>>::Output>, Error = E>
where
    I: Clone + Input + Copy,
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
