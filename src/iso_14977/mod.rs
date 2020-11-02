use pest::{iterators::Pair, Parser};

#[derive(Parser)]
#[grammar = "ebnf.pest"]
pub struct EBNFParser;

#[derive(Debug, Eq, PartialEq)]
pub struct MetaIdentifier {
    name: String,
}

#[derive(Debug, Eq, PartialEq)]
pub struct SyntaxRule {
    content: String,
}

#[derive(Debug, Eq, PartialEq)]
pub struct DefinitionList {
    content: Vec<SingleDefinition>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct SingleDefinition {
    definition: Vec<SyntacticTerm>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct SyntacticException {
    content: String,
}

#[derive(Debug, Eq, PartialEq)]
pub struct SyntacticTerm {
    factor: SyntacticFactor,
    except: Option<SyntacticException>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct SyntacticFactor {
    repetition: usize,
    primary: SyntacticPrimary,
}

#[derive(Debug, Eq, PartialEq)]
pub enum SyntacticPrimary {
    Optional(DefinitionList),
    Repeated(DefinitionList),
    Grouped(DefinitionList),
    // By definition, we have no idea how to parse special sequences.
    // just pass the string to the user.
    Special(String),
    MetaIdentifier(MetaIdentifier),
    TerminalString(String),
}

impl EBNFParser {
    pub fn new(input: &str) -> Result<(), Box<dyn std::error::Error>> {
        let first_pass = EBNFParser::parse(Rule::syntax, input)?;
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

    pub fn parse_syntax_rule(pair: Pair<Rule>) -> Option<SyntaxRule> {
        match pair.as_rule() {
            Rule::syntax_rule => Some(SyntaxRule {
                content: String::from(pair.as_str()),
            }),
            _ => None,
        }
    }

    pub fn parse_definition_list(pair: Pair<Rule>) -> Option<DefinitionList> {
        let mut pair = pair.into_inner();
        Some(DefinitionList {
            content: pair
                .step_by(2)
                .map(|definition_list| EBNFParser::parse_single_definition(definition_list))
                .collect::<Option<Vec<SingleDefinition>>>()?,
        })
    }

    pub fn parse_single_definition(pair: Pair<Rule>) -> Option<SingleDefinition> {
        let mut pair = pair.into_inner();
        Some(SingleDefinition {
            definition: pair
                .step_by(2)
                .map(|syntactic_term| EBNFParser::parse_syntactic_term(syntactic_term))
                .collect::<Option<Vec<SyntacticTerm>>>()?,
        })
    }

    pub fn parse_syntactic_term(pair: Pair<Rule>) -> Option<SyntacticTerm> {
        let mut pair = pair.into_inner();
        println!("parse_syntactic_term:\n{:#?}", pair);
        None
    }

    pub fn parse_syntactic_factor(pair: Pair<Rule>) -> Option<SyntacticFactor> {
        let mut pair = pair.into_inner();
        println!("parse_syntactic_factor:\n{:#?}", pair);
        match (pair.next(), pair.next(), pair.next()) {
            (Some(integer), Some(repetition_symbol), Some(syntactic_primary)) => match (
                integer.as_rule(),
                repetition_symbol.as_rule(),
                syntactic_primary.as_rule(),
            ) {
                (Rule::integer, Rule::repetition_symbol, Rule::syntactic_primary) => {
                    Some(SyntacticFactor {
                        repetition: integer
                            .as_str()
                            .parse::<usize>()
                            .expect("Unable to parse integer required for syntactic_factor."),
                        primary: EBNFParser::parse_syntactic_primary(syntactic_primary)?,
                    })
                }
                _ => panic!("parse_syntactic_factor is unable to match with the pattern (integer, repetition_symbol, syntactic_primary)"),
            },
            (Some(syntactic_primary), None, None) => match syntactic_primary.as_rule() {
                Rule::syntactic_primary => Some(SyntacticFactor {
                    repetition: 1,
                    primary: EBNFParser::parse_syntactic_primary(syntactic_primary)?,
                }),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn parse_syntactic_primary(pair: Pair<Rule>) -> Option<SyntacticPrimary> {
        let mut pair = pair.into_inner().next()?;
        Some(match pair.as_rule() {
            Rule::optional_sequence => {
                SyntacticPrimary::Optional(EBNFParser::parse_definition_list(pair)?)
            }
            Rule::repeated_sequence => {
                SyntacticPrimary::Repeated(EBNFParser::parse_definition_list(pair)?)
            }
            Rule::grouped_sequence => {
                SyntacticPrimary::Grouped(EBNFParser::parse_definition_list(pair)?)
            }
            Rule::meta_identifier => {
                SyntacticPrimary::MetaIdentifier(EBNFParser::parse_meta_identifier(pair)?)
            }
            Rule::terminal_string => SyntacticPrimary::TerminalString(String::from(pair.as_str())),
            Rule::special_sequence => SyntacticPrimary::Special(String::from(pair.as_str())),
            _ => panic!(
                r#"
            parse_syntactic_primary is unable to match any of the expected enum.
            Instead, we got {:#?}"#,
                pair
            ),
        })
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
            );
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
        if let Some(pair) = EBNFParser::parse(Rule::syntactic_factor, r#"5 * {"abcde"}"#)?.next() {
            let result = EBNFParser::parse_syntactic_factor(pair);
            println!("result:\n{:#?}", result);
        };
        Ok(())
    }

    #[test]
    fn parse_definition_list() -> Result<(), Box<dyn std::error::Error>> {
        if let Some(pair) = EBNFParser::parse(
            Rule::definition_list,
            r#"(5 * {"abcde"} - "xyz") | "fghi", "ghi";"#,
        )?
        .next()
        {
            EBNFParser::parse_definition_list(pair);
        };
        Ok(())
    }

    #[test]
    fn parse_syntax_rule() -> Result<(), Box<dyn std::error::Error>> {
        if let Some(pair) = EBNFParser::parse(Rule::syntax_rule, r#"letter = "a" | "b";"#)?.next() {
            let mut pair = pair.into_inner();
            match (pair.next(), pair.next(), pair.next(), pair.next()) {
                (
                    Some(meta_identifier),
                    Some(defining_symbol),
                    Some(definition_list),
                    Some(terminator_symbol),
                ) => match (
                    meta_identifier.as_rule(),
                    defining_symbol.as_rule(),
                    definition_list.as_rule(),
                    terminator_symbol.as_rule(),
                ) {
                    (
                        Rule::meta_identifier,
                        Rule::defining_symbol,
                        Rule::definition_list,
                        Rule::terminator_symbol,
                    ) => {
                        assert_eq!(
                            Some(MetaIdentifier {
                                name: "letter".to_string(),
                            }),
                            EBNFParser::parse_meta_identifier(meta_identifier)
                        );
                        assert_eq!(r#""a" | "b""#, definition_list.as_str());
                    }
                    _ => {}
                },
                _ => {}
            };
        };
        Ok(())
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
