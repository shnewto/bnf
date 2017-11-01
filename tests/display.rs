extern crate bnf;

#[cfg(test)]
mod tests {
    use super::*;

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
                              <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL> | <personal-part> <name-part>\n\
                              <personal-part> ::= <initial> \".\" | <first-name>\n\
                              <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>\n\
                              <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>\n\
                              <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\"\n\
                              <opt-apt-num> ::= <apt-num> | \"\"\n";

        let grammar = bnf::parse(input);

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
                              <name-part> ::= <personal-part> <last-name> <opt-suffix-part> <EOL> | <personal-part> <name-part>\n\
                              <personal-part> ::= <initial> \".\" | <first-name>\n\
                              <street-address> ::= <house-num> <street-name> <opt-apt-num> <EOL>\n\
                              <zip-part> ::= <town-name> \",\" <state-code> <ZIP-code> <EOL>\n\
                              <opt-suffix-part> ::= \"Sr.\" | \"Jr.\" | <roman-numeral> | \"\"\n\
                              <opt-apt-num> ::= <apt-num> | \"\"\n";

        let grammar = bnf::parse(input);

        assert_eq!(grammar.to_string(), display_output);
    }
}
