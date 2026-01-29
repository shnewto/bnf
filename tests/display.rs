#![cfg(test)]

use bnf::Grammar;

#[test]
fn validate_terminated_display() {
    let input = std::include_str!("./fixtures/postal_address.terminated.input.bnf");
    let display_output = "<postal-address> ::= <name-part> <street-address> <zip-part>\n\
                          <name-part> ::= <personal-part> <last-name> \
                          <opt-suffix-part> <EOL> | <personal-part> <name-part>\n\
                          <personal-part> ::= <initial> '.' | <first-name>\n\
                          <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>\n\
                          <zip-part> ::= <town-name> ',' <state-code> <ZIP-code> <EOL>\n\
                          <opt-suffix-part> ::= 'Sr.' | 'Jr.' | <roman-numeral> | ''\n\
                          <opt-apt-num> ::= <apt-num> | ''\n\
                          <initial> ::= 'A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J' | 'K' | 'L' | 'M' | 'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T' | 'U' | 'V' | 'W' | 'X' | 'Y' | 'Z'\n\
                          <first-name> ::= <name-word>\n\
                          <last-name> ::= <name-word>\n\
                          <name-word> ::= <letter> | <letter> <name-word>\n\
                          <house-num> ::= <digit> | <digit> <house-num>\n\
                          <apt-num> ::= <digit> | <digit> <apt-num>\n\
                          <street-name> ::= <word> | <word> ' ' <street-name>\n\
                          <town-name> ::= <word> | <word> ' ' <town-name>\n\
                          <word> ::= <letter> | <letter> <word>\n\
                          <state-code> ::= <letter> <letter>\n\
                          <ZIP-code> ::= <digit> <digit> <digit> <digit> <digit>\n\
                          <roman-numeral> ::= 'I' | 'II' | 'III' | 'IV' | 'V' | 'VI' | 'VII' | 'VIII' | 'IX' | 'X'\n\
                          <EOL> ::= ';'\n\
                          <letter> ::= 'A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J' | 'K' | 'L' | 'M' | 'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T' | 'U' | 'V' | 'W' | 'X' | 'Y' | 'Z' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j' | 'k' | 'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't' | 'u' | 'v' | 'w' | 'x' | 'y' | 'z'\n\
                          <digit> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'\n";

    let grammar: Grammar = input.parse().unwrap();

    assert_eq!(grammar.to_string(), display_output);
}

#[test]
fn validate_nonterminated_display() {
    let input = std::include_str!("./fixtures/postal_address.nonterminated.input.bnf");
    let display_output = "<postal-address> ::= <name-part> <street-address> <zip-part>\n\
                          <name-part> ::= <personal-part> <last-name> \
                          <opt-suffix-part> <EOL> | <personal-part> <name-part>\n\
                          <personal-part> ::= <initial> '.' | <first-name>\n\
                          <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>\n\
                          <zip-part> ::= <town-name> ',' <state-code> <ZIP-code> <EOL>\n\
                          <opt-suffix-part> ::= 'Sr.' | 'Jr.' | <roman-numeral> | ''\n\
                          <opt-apt-num> ::= <apt-num> | ''\n";

    let grammar: Grammar = input.parse().unwrap();

    assert_eq!(grammar.to_string(), display_output);
}

#[test]
fn grammar_with_quotes() {
    let input = "
        <permissive-string-definition>
            ::= <single-quote> <message> <single-quote>
            | <double-quote> <messag> <double-quote>

        <double-quote>
            ::= '\"'

        <single-quote>
            ::= \"'\"

        <message>
            ::= \"Hello, world!\"
    ";

    let display_output = "\
                          <permissive-string-definition> \
                          ::= <single-quote> <message> <single-quote> \
                          | <double-quote> <messag> <double-quote>\n\
                          <double-quote> \
                          ::= \'\"\'\n\
                          <single-quote> \
                          ::= \"\'\"\n\
                          <message> \
                          ::= 'Hello, world!'\n\
                          ";

    let grammar: Grammar = input.parse().expect("Grammar with quotes should parse");
    assert_eq!(grammar.to_string(), display_output);
}
