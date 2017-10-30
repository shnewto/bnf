
use nom::{Err, Needed};

pub fn report_error(err: Err<&[u8], u32>) {
    match err {
        Err::Code(_) => {
            println!("Parsing error: Unknown origin");
        }
        Err::Node(_, n) => {
            println!("Parsing error: Unknown origin");
            for e in n {
                report_error(e);
            }
        }
        Err::Position(_, p) => {
            println!(
                "Parsing error: When input is {}",
                String::from_utf8_lossy(p)
            );
        }
        Err::NodePosition(_, p, n) => {
            println!(
                "Parsing error: When input is {}",
                String::from_utf8_lossy(p)
            );
            for e in n {
                report_error(e);
            }
        }
    }
}

pub fn report_incomplete(needed: Needed, actual: usize) {
    match needed {
        Needed::Unknown => {
            println!(
                "Data error: insufficient size, expectation unknown, \
                 found {} bytes",
                actual
            );
        }
        Needed::Size(s) => {
            println!(
                "Data error: insufficient size, expected {} bytes \
                 but found {}",
                s,
                actual
            );
        }
    }
}
