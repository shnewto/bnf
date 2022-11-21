mod grammar;
mod input_range;
mod traversal;

use crate::ParseTree;

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input: &'gram str,
) -> impl Iterator<Item = ParseTree<'gram>> {
    todo!();
    std::iter::empty()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;

    #[test]
    fn parse_dna_left_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <dna> <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_dna_right_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_ambiguous() {
        let grammar: Grammar = "<start> ::= <a> | <b>
        <a> ::= \"END\"
        <b> ::= \"END\""
            .parse()
            .unwrap();

        let input = "END";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 2);
    }

    #[test]
    fn parse_complete_empty() {
        let grammar: Grammar = "<start> ::= \"hi\" <empty>
        <empty> ::= \"\""
            .parse()
            .unwrap();

        let input = "hi";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_empty() {
        let grammar: Grammar = "<start> ::= \"\"".parse().unwrap();

        let input = "";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_nested_empty_post() {
        let grammar: Grammar = "
        <start> ::= <a> <empty>
        <a> ::= 'a' <empty>
        <empty> ::= ''"
            .parse()
            .unwrap();

        let input = "a";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);

        let tree = parse(&grammar, input).next().unwrap();
        println!("{tree}");
    }

    // #[test]
    // fn parse_nested_empty_pre() {
    //     let grammar: Grammar = "
    //     <start> ::= <empty> <a>
    //     <a> ::= <empty> 'a'
    //     <empty> ::= ''"
    //         .parse()
    //         .unwrap();

    //     let input = "a";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

    // #[test]
    // fn parse_nested_empty_pre_and_post() {
    //     let grammar: Grammar = "
    //     <start> ::= <empty> <a> <empty>
    //     <a> ::= <empty> 'a' <empty>
    //     <empty> ::= ''"
    //         .parse()
    //         .unwrap();

    //     let input = "a";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

    // #[test]
    // fn parse_inline_empty() {
    //     let grammar: Grammar = "
    //     <start> ::= <a> '' <a>
    //     <a> ::= 'a'"
    //         .parse()
    //         .unwrap();

    //     let input = "aa";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

    // TODO: test case for <start> ::= <a> | <b>, with both <a> and <b> nullable should give two parses
    // TODO: test case for <nonterm> without a rule
    // TODO: property test which inserts empty rule terms and should still parse

    // (source: <https://loup-vaillant.fr/tutorials/earley-parsing/empty-rules>)
    // #[test]
    // fn parse_empty_infinite() {
    //     let grammar: Grammar = "
    //     <a> ::= '' | <b>
    //     <b> ::= <a>"
    //         .parse()
    //         .unwrap();

    //     let input = "";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

    // (source: <https://loup-vaillant.fr/tutorials/earley-parsing/recogniser>)
    // Sum     -> Sum     [+-] Product
    // Sum     -> Product
    // Product -> Product [*/] Factor
    // Product -> Factor
    // Factor  -> '(' Sum ')'
    // Factor  -> Number
    // Number  -> [0-9] Number
    // Number  -> [0-9]
    #[test]
    fn parse_math() {
        let grammar: Grammar = "<sum> ::= <sum> <add> <product>
            <sum> ::= <product>
            <product> ::= <product> <mult> <factor>
            <product> ::= <factor>
            <add> ::= \"+\" | \"-\"
            <mult> ::= \"*\" | \"/\"
            <factor> ::= \"(\" <sum> \")\"
            <factor> ::= <number>
            <number> ::= <digit> <number>
            <number> ::= <digit>
            <digit> ::= \"0\" | \"1\" | \"2\" | \"3\" | \"4\" | \"5\" | \"6\" | \"7\" | \"8\" | \"9\"
        ".parse().unwrap();

        let input = "1+(2*3-4)";

        let parses: Vec<_> = parse(&grammar, input).collect();

        let expected_parse_tree = "
<sum> ::= <sum> <add> <product>
├── <sum> ::= <product>
│   └── <product> ::= <factor>
│       └── <factor> ::= <number>
│           └── <number> ::= <digit>
│               └── <digit> ::= \"1\"
│                   └── \"1\"
├── <add> ::= \"+\"
│   └── \"+\"
└── <product> ::= <factor>
    └── <factor> ::= \"(\" <sum> \")\"
        ├── \"(\"
        ├── <sum> ::= <sum> <add> <product>
        │   ├── <sum> ::= <product>
        │   │   └── <product> ::= <product> <mult> <factor>
        │   │       ├── <product> ::= <factor>
        │   │       │   └── <factor> ::= <number>
        │   │       │       └── <number> ::= <digit>
        │   │       │           └── <digit> ::= \"2\"
        │   │       │               └── \"2\"
        │   │       ├── <mult> ::= \"*\"
        │   │       │   └── \"*\"
        │   │       └── <factor> ::= <number>
        │   │           └── <number> ::= <digit>
        │   │               └── <digit> ::= \"3\"
        │   │                   └── \"3\"
        │   ├── <add> ::= \"-\"
        │   │   └── \"-\"
        │   └── <product> ::= <factor>
        │       └── <factor> ::= <number>
        │           └── <number> ::= <digit>
        │               └── <digit> ::= \"4\"
        │                   └── \"4\"
        └── \")\"\n"
            .trim_start();

        assert_eq!(parses.len(), 1);
        let parse_tree = format!("{}", parses[0]);
        assert_eq!(parse_tree, expected_parse_tree)
    }
}
