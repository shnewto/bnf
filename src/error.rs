use std::fmt;
use std::error;
use nom::{Err, Needed};

#[derive(PartialEq, Debug, Clone)]
pub enum Error {
    ParseError(String),
    ParseIncomplete(String),
    GenerateError(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::ParseError(ref s) => write!(f, "{}", s),
            Error::ParseIncomplete(ref s) => write!(f, "{}", s),
            Error::GenerateError(ref s) => write!(f, "{}", s),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        "BNF error"
    }
}

impl<'a> From<Err<&'a [u8]>> for Error {
    fn from(err: Err<&[u8]>) -> Self {
        let string = match err {
            Err::Code(_) => String::from("Parsing error: Unknown origin"),
            Err::Node(_, n) => n.iter()
                .fold(String::from("Parsing error: Unknown origin."), |s, e| {
                    s + &format!(" {}", e)
                }),
            Err::Position(_, p) => format!(
                "Parsing error: When input is {}",
                String::from_utf8_lossy(p)
            ),
            Err::NodePosition(_, p, n) => n.iter().fold(
                format!(
                    "Parsing error: When input is {}.",
                    String::from_utf8_lossy(p)
                ),
                |s, e| s + &format!(" {}", e),
            ),
        };

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
    use nom::IResult;
    use error::Error;

    named!(give_error_kind, 
        do_parse!(
            tag!("1234") >>
            res: tag!("5678") >>
            (res)
        )
    );

    #[test]
    fn gets_error_error() {
        let nom_result = give_error_kind("12340".as_bytes());
        let nom_error;
        match nom_result {
            IResult::Error(e) => nom_error = e,
            _ => panic!("gets_error_error should result in IResult::Error"),
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
            IResult::Incomplete(e) => nom_error = e,
            _ => panic!("gets_error_error should result in IResult::Error"),
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
    fn uses_error_generate() {
        let bnf_error = Error::GenerateError(String::from("Error Generating!"));
        match bnf_error {
            Error::GenerateError(_) => (),
            e => panic!("should match on generate error: {:?}", e),
        }        
    }
}