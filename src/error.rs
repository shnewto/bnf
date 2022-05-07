use std::error;
use std::fmt;
use std::str;

use nom::{
    error::{VerboseError, VerboseErrorKind},
    Err,
};

#[derive(PartialEq, Debug, Clone)]
pub enum Error {
    ParseError(String),
    GenerateError(String),
    RecursionLimit(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::ParseError(ref s) => write!(f, "{}", s),
            Error::GenerateError(ref s) => write!(f, "{}", s),
            Error::RecursionLimit(ref s) => write!(f, "{}", s),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        "BNF error"
    }
}

impl<'a> From<VerboseError<(&'a str, VerboseErrorKind)>> for Error {
    fn from(err: VerboseError<(&str, VerboseErrorKind)>) -> Self {
        Error::ParseError(format!("Parsing error: {:?}", err))
    }
}

impl<'a> From<Err<VerboseError<&str>>> for Error {
    fn from(err: Err<VerboseError<&str>>) -> Self {
        Error::ParseError(format!("Parsing error: {:?}", err))
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

    fn give_error_kind<'a>(input: &'a str) -> IResult<&'a str, &str, VerboseError<&'a str>> {
        let (input, _) = tag("1234")(input)?;
        let (input, res) = tag("5678")(input)?;
        Ok((input, res))
    }

    #[test]
    fn gets_error_error() {
        let nom_result = give_error_kind("12340");
        let nom_error;
        match nom_result {
            Result::Err(e) => match e {
                Err::Error(_) => nom_error = e,
                _ => panic!("gets_error_error should result in IResult::Err(Err::Error(e))"),
            },
            _ => panic!("gets_error_error should result in IResult::Err"),
        }

        let bnf_error: Result<String, Error> = Err(Error::from(nom_error));

        assert!(
            bnf_error.is_err(),
            "production result should be error {:?}",
            bnf_error
        );

        match bnf_error.unwrap_err() {
            Error::ParseError(_) => (),
            e => panic!("production error should be error parsing: {:?}", e),
        }
    }

    #[test]
    fn gets_error_on_incomplete() {
        let nom_result = give_error_kind("");
        let nom_error;
        match nom_result {
            Result::Err(e) => nom_error = e,
            _ => panic!("gets_error_error should result in IResult::Err"),
        }

        let bnf_error: Result<String, Error> = Err(Error::from(nom_error));

        assert!(
            bnf_error.is_err(),
            "production result should be error {:?}",
            bnf_error
        );
        match bnf_error.unwrap_err() {
            Error::ParseError(_) => (),
            e => panic!("production error should be parse error: {:?}", e),
        }
    }

    #[test]
    fn uses_error_recursion_limit() {
        let bnf_error = Error::RecursionLimit(String::from("reucrsion limit reached!"));
        match bnf_error {
            Error::RecursionLimit(_) => (),
            e => panic!("should match on reursion limit: {:?}", e),
        }
    }

    #[test]
    fn uses_error_generate() {
        let bnf_error = Error::GenerateError(String::from("error generating!"));
        match bnf_error {
            Error::GenerateError(_) => (),
            e => panic!("should match on generate error: {:?}", e),
        }
    }

    #[test]
    fn test_error_display() {
        let parse_error = Error::ParseError(String::from("parsing error!"));
        let generate_error = Error::GenerateError(String::from("error generating!"));
        let recursion_error = Error::RecursionLimit(String::from("recursion limit reached!"));

        assert_eq!(parse_error.to_string(), String::from("parsing error!"));
        assert_eq!(
            generate_error.to_string(),
            String::from("error generating!")
        );
        assert_eq!(
            recursion_error.to_string(),
            String::from("recursion limit reached!")
        );
    }
}
