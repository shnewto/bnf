use pest::{iterators::Pair, Parser};

#[derive(Parser)]
#[grammar = "ebnf.pest"]
pub struct EBNFParser;

#[derive(Debug, Eq, PartialEq)]
pub struct MetaIdentifier {
    name: String,
}

impl EBNFParser {
    pub fn new(input: &str) -> Result<(), Box<dyn std::error::Error>> {
        let first_pass = EBNFParser::parse(Rule::syntax, input)?;
        println!("first_pass:{:#?}", first_pass);
        Ok(())
    }

    pub fn parse_meta_identifier(pair: Pair<Rule>) -> Option<MetaIdentifier> {
        match pair.as_rule() {
            Rule::meta_identifier => Some(MetaIdentifier {
                name: String::from(pair.as_str()),
            }),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use pest::Parser;

    #[test]
    fn parse_meta_identifier() -> Result<(), Box<dyn std::error::Error>> {
        if let Some(pair) = EBNFParser::parse(Rule::meta_identifier, r#"letter"#)?.next() {
            assert_eq!(
                EBNFParser::parse_meta_identifier(pair),
                Some(MetaIdentifier {
                    name: "letter".to_string()
                })
            )
        };

        Ok(())
    }

    #[test]
    fn parse_symbols() -> Result<(), Box<dyn std::error::Error>> {
        let successful_parse = EBNFParser::parse(Rule::defining_symbol, r#"="#)?;
        println!("{:?}", successful_parse);
        let successful_parse = EBNFParser::parse(Rule::definition_separator_symbol, r#"|"#)?;
        println!("{:?}", successful_parse);
        let successful_parse = EBNFParser::parse(Rule::first_quote_symbol, r#"’"#)?;
        println!("{:?}", successful_parse);
        let successful_parse = EBNFParser::parse(Rule::second_quote_symbol, r#"""#)?;
        println!("{:?}", successful_parse);
        let successful_parse = EBNFParser::parse(Rule::repetition_symbol, r#"*"#)?;
        println!("{:?}", successful_parse);
        Ok(())
    }

    #[test]
    fn parse_terminal_string() {
        let successful_parse = EBNFParser::parse(Rule::terminal_string, r#""b \r a \n d""#);
        println!("{:?}", successful_parse);
        let successful_parse = EBNFParser::parse(Rule::terminal_string, r#"’a’"#);
        println!("{:?}", successful_parse);
    }

    #[test]
    fn parse_syntactic_factor() -> Result<(), Box<dyn std::error::Error>> {
        let successful_parse = EBNFParser::parse(Rule::syntactic_factor, r#"5 * "abcde""#)?;
        let successful_parse = EBNFParser::parse(Rule::syntactic_factor, r#"5 * {"abcde"}"#)?;
        Ok(())
    }

    #[test]
    fn parse_definition_list() -> Result<(), Box<dyn std::error::Error>> {
        let _ = EBNFParser::parse(
            Rule::definition_list,
            r#"(5 * {"abcde"} - "xyz") | "fghi";"#,
        )?;
        Ok(())
    }

    #[test]
    fn parse_syntax_rule() {
        let successful_parse = EBNFParser::parse(Rule::syntax, r#"letter = "a" | "b";"#);
        println!("{:#?}", successful_parse);
    }

    #[test]
    fn parse_syntax_rule_weird() {
        let successful_parse = EBNFParser::parse(
            Rule::syntax,
            r#"
        (* hello 3.5 *) letter 
        = "a" | "b";"#,
        );
        println!("{:#?}", successful_parse);
    }

    #[test]
    fn parse_ebnf_itself() {
        EBNFParser::new(
            r#"
            (*
            The syntax of Extended BNF can be defined using
            itself. There are four parts in this example,
            the first part names the characters, the second
            part defines the removal of unnecessary nonprinting characters, the third part defines the
            removal of textual comments, and the final part
            defines the structure of Extended BNF itself.
            Each syntax rule in this example starts with a
            comment that identifies the corresponding clause
            in the standard.
            The meaning of special-sequences is not defined
            in the standard. In this example (see the
            reference to 7.6) they represent control
            functions defined by ISO/IEC 6429:1992.
            Another special-sequence defines a
            syntactic-exception (see the reference to 4.7).
            *)
            (*
            The first part of the lexical syntax defines the
            characters in the 7-bit character set (ISO/IEC
            646:1991) that represent each terminal-character
            and gap-separator in Extended BNF.
            *)
            (* see 7.2 *) 
            letter = ’a’ | ’b’ | ’c’ | ’d’ | ’e’ | ’f’ | ’g’ | ’h’
            | ’i’ | ’j’ | ’k’ | ’l’ | ’m’ | ’n’ | ’o’ | ’p’
            | ’q’ | ’r’ | ’s’ | ’t’ | ’u’ | ’v’ | ’w’ | ’x’
            | ’y’ | ’z’
            | ’A’ | ’B’ | ’C’ | ’D’ | ’E’ | ’F’ | ’G’ | ’H’
            | ’I’ | ’J’ | ’K’ | ’L’ | ’M’ | ’N’ | ’O’ | ’P’
            | ’Q’ | ’R’ | ’S’ | ’T’ | ’U’ | ’V’ | ’W’ | ’X’
            | ’Y’ | ’Z’;
            (* see 7.2 *) decimal_digit
            = ’0’ | ’1’ | ’2’ | ’3’ | ’4’ | ’5’ | ’6’ | ’7’
            | ’8’ | ’9’;
            (*
            The representation of the following
            terminal-characters is defined in clauses 7.3,
            7.4 and tables 1, 2.
            *)
            concatenate_symbol = ’,’;
            defining_symbol = ’=’;
            definition_separator_symbol = ’|’ | ’//’ | ’!’;
            end_comment_symbol = ’*)’;
            end_group_symbol = ’)’;
            end_option_symbol = ’]’ | ’/)’;
            end_repeat_symbol = ’}’ | ’:)’;
            except_symbol = ’-’;
            first_quote_symbol = "’";
            repetition_symbol = ’*’;
            second_quote_symbol = ’"’;
            special_sequence_symbol = ’?’;
            start_comment_symbol = ’(*’;
            start_group_symbol = ’(’;
            start_option_symbol = ’[’ | ’(//’;
            start_repeat_symbol = ’{’ | ’(:’;
            terminator_symbol = ’;’ | ’.’;
            (* see 7.5 *) other_character
            = ’ ’ | ’:’ | ’+’ | ’_’ | ’%’ | ’@’
            | ’&’ | ’#’ | ’$’ | ’<’ | ’>’ | ’\’
            | ’ˆ’ | ’‘’ | ’˜’;
            (* see 7.6 *) space_character = ’ ’;                
            "#,
        ).unwrap();
    }
}
