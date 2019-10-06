extern crate bnf;

use bnf::Grammar;

#[test]
fn validate_terminated_display() {
    let input = "<postal-address> ::= <name-part> <street-address> <zip-part>;

            <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
                            | <personal-part> <name-part>;

        <personal-part> ::= <initial> \".\" | <first-name>;

        <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>;

            <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>;

        <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\";
            <opt-apt-num> ::= <apt-num> | \"\";";

    let display_output = "<postal-address> ::= <name-part> <street-address> <zip-part>\n\
                          <name-part> ::= <personal-part> <last-name> \
                          <opt-suffix-part> <EOL> | <personal-part> <name-part>\n\
                          <personal-part> ::= <initial> \".\" | <first-name>\n\
                          <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>\n\
                          <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>\n\
                          <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\"\n\
                          <opt-apt-num> ::= <apt-num> | \"\"\n";

    let grammar = Grammar::from_str(input).unwrap();

    assert_eq!(grammar.to_string(), display_output);
}

#[test]
fn validate_nonterminated_display() {
    let input = "<postal-address> ::= <name-part> <street-address> <zip-part>

            <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL>
                            | <personal-part> <name-part>

        <personal-part> ::= <initial> \".\" | <first-name>

        <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>

            <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>

        <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\"
            <opt-apt-num> ::= <apt-num> | \"\"";

    let display_output = "<postal-address> ::= <name-part> <street-address> <zip-part>\n\
                          <name-part> ::= <personal-part> <last-name> \
                          <opt-suffix-part> <EOL> | <personal-part> <name-part>\n\
                          <personal-part> ::= <initial> \".\" | <first-name>\n\
                          <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>\n\
                          <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>\n\
                          <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\"\n\
                          <opt-apt-num> ::= <apt-num> | \"\"\n";

    let grammar = Grammar::from_str(input).unwrap();

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
                          ::= \"Hello, world!\"\n\
                          ";

    let grammar = Grammar::from_str(input).expect("Grammar with quotes should parse");
    assert_eq!(grammar.to_string(), display_output);
}
