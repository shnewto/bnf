use std::fmt;
use std::error;
use nom::{Err, Needed};

#[derive(PartialEq, Debug, Clone)]
pub enum Error {
    ParseError(String),
    ParseIncomplete(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::ParseError(ref s) => write!(f, "ParseError: {}", s),
            Error::ParseIncomplete(ref s) => write!(f, "ParseIncomplete: {}", s),
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
