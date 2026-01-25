use nom::{Input, Parser, error::ParseError};

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

#[cfg(test)]
mod tests {
    use super::*;
    use nom::{Err, IResult, bytes::complete::tag, error::ErrorKind};

    fn test_parser(input: &str) -> IResult<&str, &str> {
        tag("test")(input)
    }

    fn test_delimiter(input: &str) -> IResult<&str, &str> {
        tag(",")(input)
    }

    fn failing_parser(input: &str) -> IResult<&str, &str> {
        Err(Err::Failure(nom::error::Error::new(input, ErrorKind::Tag)))
    }

    #[test]
    fn test_xt_list_with_separator_success() {
        let mut parser = xt_list_with_separator(test_parser, test_delimiter);
        let result = parser.parse("test,test,test");
        assert!(result.is_ok());
        let (remaining, items) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(items.len(), 3);
    }

    #[test]
    fn test_xt_list_with_separator_single_item() {
        let mut parser = xt_list_with_separator(test_parser, test_delimiter);
        let result = parser.parse("test");
        assert!(result.is_ok());
        let (remaining, items) = result.unwrap();
        assert_eq!(remaining, "");
        assert_eq!(items.len(), 1);
    }

    #[test]
    fn test_xt_list_with_separator_parser_failure() {
        // Test the Err(e) return path when parser fails with non-Error variant
        let mut parser = xt_list_with_separator(failing_parser, test_delimiter);
        let result = parser.parse("test");
        assert!(matches!(result, Err(Err::Failure(_))));
    }

    #[test]
    fn test_xt_list_with_separator_delimiter_failure() {
        // Test the Err(e) return path when delimiter fails with non-Error variant
        // This tests line 27: Err(e) => return Err(e)
        // We need a parser that succeeds but delimiter fails with Failure
        fn failing_delimiter(input: &str) -> IResult<&str, &str> {
            Err(Err::Failure(nom::error::Error::new(input, ErrorKind::Tag)))
        }

        let mut parser = xt_list_with_separator(test_parser, failing_delimiter);
        let result = parser.parse("test,");
        assert!(matches!(result, Err(Err::Failure(_))));
    }
}
