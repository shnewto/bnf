use nom::{Err, Needed, error::ErrorKind};
use std::error;
use std::fmt;
use std::str;

#[derive(PartialEq, Debug, Clone)]
pub enum Error {
    ParseError(String),
    ParseIncomplete(String),
    GenerateError(String),
    RecursionLimit(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::ParseError(ref s) => write!(f, "{}", s),
            Error::ParseIncomplete(ref s) => write!(f, "{}", s),
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

impl<'a> From<Err<(&'a [u8],ErrorKind)>> for Error {
    fn from(err: Err<(&[u8],ErrorKind)>) -> Self {
        match err {
            Err::Incomplete(n) => Error::from(n),
            Err::Error(e) => Error::from(e),
            Err::Failure(e) => Error::from(e)
        }
    }
}

impl<'a> From<(&'a [u8],ErrorKind)> for Error {
    fn from(err: (&[u8],ErrorKind)) -> Self {
        let string = format!("Parsing error: {}\n {:?}", err.1.description(), str::from_utf8(err.0));
        Error::ParseError(string)
    }
}

impl From<Needed> for Error {
    fn from(needed: Needed) -> Self {
        let string = match needed {
            Needed::Unknown => format!("Data error: insufficient size, expectation unknown"),
            Needed::Size(s) => format!("Data error: insufficient size, expected {} bytes", s),
        };

        Error::ParseIncomplete(string)
    }
}

#[cfg(test)]
mod tests {
    use error::Error;
    use nom::Err;

    named!(
        give_error_kind,
        do_parse!(tag!("1234") >> res: tag!("5678") >> (res))
    );

    #[test]
    fn gets_error_error() {
        let nom_result = give_error_kind("12340".as_bytes());
        let nom_error;
        match nom_result {
            Result::Err(e) => match e {
                Err::Error(_) => nom_error = e,
                _ => panic!("gets_error_error should result in IResult::Err(Err::Error(e))")
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
    fn gets_error_incomplete() {
        let nom_result = give_error_kind("".as_bytes());
        let nom_error;
        match nom_result {
            Result::Err(e) => match e {
                Err::Incomplete(n) => nom_error = n,
                _ => panic!("gets_error_error should result in IResult::Err(Err::Incomplete(n))")
            }
            _ => panic!("gets_error_error should result in IResult::Err"),
        }

        let bnf_error: Result<String, Error> = Err(Error::from(nom_error));

        assert!(
            bnf_error.is_err(),
            "production result should be error {:?}",
            bnf_error
        );
        match bnf_error.unwrap_err() {
            Error::ParseIncomplete(_) => (),
            e => panic!("production error should be incomplete: {:?}", e),
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
        let parse_error = Error::ParseError(String::from("syntax error!"));
        let incomplete_error = Error::ParseIncomplete(String::from("incomplete data size!"));
        let generate_error = Error::GenerateError(String::from("error generating!"));
        let recursion_error = Error::RecursionLimit(String::from("recursion limit reached!"));

        assert_eq!(parse_error.to_string(), String::from("syntax error!"));
        assert_eq!(
            incomplete_error.to_string(),
            String::from("incomplete data size!")
        );
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
