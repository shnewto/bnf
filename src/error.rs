use std::error;
use std::fmt;
use std::str;

use nom::{Err, error::ErrorKind};

#[derive(PartialEq, Eq, Debug, Clone)]
#[non_exhaustive]
pub enum Error {
    ParseError(String),
    GenerateError(String),
    ValidationError(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::ParseError(s) | Error::GenerateError(s) | Error::ValidationError(s) => {
                write!(f, "{s}")
            }
        }
    }
}

impl error::Error for Error {}

impl From<nom::error::Error<&str>> for Error {
    fn from(err: nom::error::Error<&str>) -> Self {
        Error::ParseError(format!("Parsing error: {err:?}"))
    }
}

impl From<Err<nom::error::Error<&str>>> for Error {
    fn from(err: Err<nom::error::Error<&str>>) -> Self {
        Error::ParseError(format!("Parsing error: {err:?}"))
    }
}

impl From<(&'_ str, ErrorKind)> for Error {
    fn from(err: (&str, ErrorKind)) -> Self {
        let string = format!("Parsing error: {:?}\n {:?}", err.1, err.0);
        Error::ParseError(string)
    }
}

#[cfg(test)]
mod tests {
    use crate::error::Error;
    use nom::{Err, IResult, bytes::complete::tag};

    fn give_error_kind(input: &str) -> IResult<&str, &str> {
        let (input, _) = tag("1234")(input)?;
        let (input, res) = tag("5678")(input)?;
        Ok((input, res))
    }

    #[test]
    fn gets_error_error() {
        let nom_result = give_error_kind("12340");
        assert!(matches!(nom_result, Err(Err::Error(_))));
    }

    #[test]
    fn gets_error_on_incomplete() {
        let nom_result = give_error_kind("").map_err(Error::from);
        assert!(matches!(nom_result, Err(Error::ParseError(_))));
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
        let validation_error = Error::ValidationError(String::from("validation error!"));

        assert_eq!(parse_error.to_string(), String::from("parsing error!"));
        assert_eq!(
            generate_error.to_string(),
            String::from("error generating!")
        );
        assert_eq!(
            validation_error.to_string(),
            String::from("validation error!")
        );
    }

    #[test]
    fn from_nom_verbose_error() {
        let error = nom::error::Error::new("test", nom::error::ErrorKind::Tag);
        assert!(matches!(Error::from(error), Error::ParseError(_)));
    }

    #[test]
    fn from_str_and_nom_verbose_error_kind() {
        let description = "anything";
        let error_kind = nom::error::ErrorKind::Char;
        assert!(matches!(
            Error::from((description, error_kind)),
            Error::ParseError(_)
        ));
    }

    #[test]
    fn clone_error() {
        let error = Error::ParseError(String::from("parsing error!"));
        let clone = error.clone();
        assert_eq!(error, clone);
    }

    #[test]
    fn from_nom_err_failure() {
        let error = nom::error::Error::new("test", nom::error::ErrorKind::Tag);
        let err = Err::Failure(error);
        let bnf_error = Error::from(err);
        assert!(matches!(bnf_error, Error::ParseError(_)));
        assert!(bnf_error.to_string().contains("Parsing error:"));
    }

    #[test]
    fn from_nom_err_incomplete() {
        let err = Err::Incomplete(nom::Needed::Unknown);
        let bnf_error = Error::from(err);
        assert!(matches!(bnf_error, Error::ParseError(_)));
        assert!(bnf_error.to_string().contains("Parsing error:"));
    }

    #[test]
    fn error_trait_impl() {
        // Test that Error implements std::error::Error
        let error = Error::ParseError(String::from("test"));
        let error_ref: &dyn std::error::Error = &error;
        assert_eq!(error_ref.to_string(), "test");
    }
}
