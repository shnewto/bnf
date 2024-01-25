use std::error;
use std::fmt;
use std::str;

use nom::{
    error::{VerboseError, VerboseErrorKind},
    Err,
};

#[derive(PartialEq, Eq, Debug, Clone)]
#[non_exhaustive]
pub enum Error {
    ParseError(String),
    GenerateError(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::ParseError(ref s) | Error::GenerateError(ref s) => write!(f, "{s}"),
        }
    }
}

impl error::Error for Error {}

impl<'a> From<VerboseError<(&'a str, VerboseErrorKind)>> for Error {
    fn from(err: VerboseError<(&str, VerboseErrorKind)>) -> Self {
        Error::ParseError(format!("Parsing error: {err:?}"))
    }
}

impl From<Err<VerboseError<&str>>> for Error {
    fn from(err: Err<VerboseError<&str>>) -> Self {
        Error::ParseError(format!("Parsing error: {err:?}"))
    }
}

impl<'a> From<(&'a str, VerboseErrorKind)> for Error {
    fn from(err: (&str, VerboseErrorKind)) -> Self {
        let string = format!("Parsing error: {:?}\n {:?}", err.1, err.0);
        Error::ParseError(string)
    }
}

#[cfg(test)]
mod tests {
    use crate::error::Error;
    use nom::{bytes::complete::tag, error::VerboseError, Err, IResult};

    fn give_error_kind(input: &str) -> IResult<&str, &str, VerboseError<&str>> {
        let (input, _) = tag("1234")(input)?;
        let (input, res) = tag("5678")(input)?;
        Ok((input, res))
    }

    #[test]
    fn gets_error_error() {
        let nom_result = give_error_kind("12340");
        assert!(matches!(nom_result, Result::Err(Err::Error(_))));
    }

    #[test]
    fn gets_error_on_incomplete() {
        let nom_result = give_error_kind("").map_err(Error::from);
        assert!(matches!(nom_result, Result::Err(Error::ParseError(_))));
    }

    #[test]
    fn uses_error_generate() {
        let bnf_error = Error::GenerateError(String::from("error generating!"));
        assert!(matches!(bnf_error, Error::GenerateError(_)));
    }

    #[test]
    fn test_error_display() {
        let parse_error = Error::ParseError(String::from("parsing error!"));
        let generate_error = Error::GenerateError(String::from("error generating!"));

        assert_eq!(parse_error.to_string(), String::from("parsing error!"));
        assert_eq!(
            generate_error.to_string(),
            String::from("error generating!")
        );
    }

    #[test]
    fn from_nom_verbose_error() {
        let error = nom::error::VerboseError { errors: vec![] };
        assert!(matches!(Error::from(error), Error::ParseError(_)));
    }

    #[test]
    fn from_str_and_nom_verbose_error_kind() {
        let description = "anything";
        let verbose_kind = nom::error::VerboseErrorKind::Char('z');
        assert!(matches!(
            Error::from((description, verbose_kind)),
            Error::ParseError(_)
        ));
    }

    #[test]
    fn clone_error() {
        let error = Error::ParseError(String::from("parsing error!"));
        let clone = error.clone();
        assert_eq!(error, clone);
    }
}
