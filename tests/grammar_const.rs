//! Tests for the `grammar!` procedural macro.

#[cfg(test)]
mod tests {
    use bnf::Grammar;

    #[test]
    fn grammar_static_dna() {
        static G: Grammar = bnf::grammar! {
            <dna> ::= <base> | <base> <dna>;
            <base> ::= "A" | "C" | "G" | "T";
        };
        let parser = G.build_parser().expect("grammar is valid");
        let trees: Vec<_> = parser.parse_input("GATTACA").collect();
        assert!(!trees.is_empty(), "should parse GATTACA");
    }

    #[test]
    fn grammar_parse_starting_with() {
        static G: Grammar = bnf::grammar! {
            <s> ::= "a" <s> | "a";
        };
        let parser = G.build_parser().expect("grammar is valid");
        let start = bnf::term_const!(<s>);
        let trees: Vec<_> = parser.parse_input_starting_with("aa", &start).collect();
        assert!(!trees.is_empty(), "should parse aa starting from <s>");
    }
}
