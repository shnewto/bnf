use bnf::Grammar;
use insta::assert_snapshot;

#[test]
fn undefined_prod() {
    let grammar: Grammar = "
        <start> ::= <a> | <b>
        <a> ::= 'a'
        "
    .parse()
    .unwrap();

    let input = "a";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn dna_left_recursive() {
    let grammar: Grammar = "<dna> ::= <base> | <dna> <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
        .parse()
        .unwrap();

    let input = "GATTACA";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn dna_right_recursive() {
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
        .parse()
        .unwrap();

    let input = "GATTACA";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn ambiguous() {
    let grammar: Grammar = "<start> ::= <a> | <b>
        <a> ::= \"END\"
        <b> ::= \"END\""
        .parse()
        .unwrap();

    let input = "END";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn recursive_nested_infinite() {
    let grammar: Grammar = "
            <a> ::= <b> | 'z'
            <b> ::= <a> 
        "
    .parse()
    .unwrap();

    let input = "z";

    // there are infinite parses to this, so take the first 100 and call it good
    let parse_count = 100;
    let parses: Vec<_> = grammar
        .parse_input(input)
        .take(parse_count)
        .map(|a| a.to_string())
        .collect();
    assert_eq!(parses.len(), parse_count);
    assert_snapshot!(parses[0..=3].join("\n"));
}

#[test]
fn empty_right_recursive() {
    let grammar: Grammar = "<a> ::= '' | 'a' <a>".parse().unwrap();

    let input = "aaaaaaaaaa";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn empty_left_recursive() {
    let grammar: Grammar = "<a> ::= '' | <a> 'a'".parse().unwrap();

    let input = "aaaaaaaaaa";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn complete_empty() {
    let grammar: Grammar = "<start> ::= \"hi\" <empty>
        <empty> ::= \"\""
        .parse()
        .unwrap();

    let input = "hi";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn empty() {
    let grammar: Grammar = "<start> ::= \"\"".parse().unwrap();

    let input = "";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn nested_empty_post() {
    let grammar: Grammar = "
        <start> ::= <a> <empty>
        <a> ::= 'a' <empty>
        <empty> ::= ''"
        .parse()
        .unwrap();

    let input = "a";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn nested_empty_pre() {
    let grammar: Grammar = "
        <start> ::= <empty> <a>
        <a> ::= <empty> 'a'
        <empty> ::= ''"
        .parse()
        .unwrap();

    let input = "a";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn nested_empty_pre_and_post() {
    let grammar: Grammar = "
        <start> ::= <empty> <a> <empty>
        <a> ::= <empty> 'a' <empty>
        <empty> ::= ''"
        .parse()
        .unwrap();

    let input = "a";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn empty_inline() {
    let grammar: Grammar = "
        <start> ::= <a> '' <a>
        <a> ::= 'a'"
        .parse()
        .unwrap();

    let input = "aa";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn empty_ambiguous() {
    let grammar: Grammar = "
        <start> ::= <a> | <b>
        <a> ::= ''
        <b> ::= ''"
        .parse()
        .unwrap();

    let input = "";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn empty_first_nested() {
    // this structure exposes improper "nullable" production detection
    let grammar: Grammar = "
        <a> ::= '' | '' <b> <c>
        <b> ::= <c>
        <c> ::= <a>
        "
    .parse()
    .unwrap();

    let input = "";

    let parse_count = 100;
    let parses: Vec<_> = grammar
        .parse_input(input)
        .take(parse_count)
        .map(|a| a.to_string())
        .collect();
    assert_eq!(parses.len(), parse_count);
    assert_snapshot!(parses[0..=3].join("\n"));
}

#[test]
fn optional_whitespace() {
    let grammar: Grammar = "
        <balanced> ::= <left> <balanced> <right>
                     | ''
        
        <left> ::= <opt-ws> '(' <opt-ws>
        <right> ::= <opt-ws> ')' <opt-ws>
        
        <opt-ws> ::= '' | <ws>
        <ws> ::= ' ' | ' ' <ws>
        "
    .parse()
    .unwrap();

    let input = "()";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn qualified_whitespace() {
    let grammar: Grammar = "
        <terms> ::= <terms> <ws> <term>
                  | <term>
        <term> ::= <qualified>
                 | 'unqualified'
        <qualified> ::= 'QUALIFIER:' <qual-term>
        <qual-term> ::= <qual-term> <ws>
                      | 'qualified'
        <ws> ::= ' ' | ' ' <ws>
        "
    .parse()
    .unwrap();

    let input = "QUALIFIER:qualified unqualified";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

// (source: <https://loup-vaillant.fr/tutorials/earley-parsing/empty-rules>)
#[test]
fn empty_noop_infinite() {
    let grammar: Grammar = "
        <a> ::= '' | <b>
        <b> ::= <a>"
        .parse()
        .unwrap();

    let input = "";

    let parse_count = 100;
    let parses: Vec<_> = grammar
        .parse_input(input)
        .take(parse_count)
        .map(|a| a.to_string())
        .collect();
    assert_eq!(parses.len(), parse_count);
    assert_snapshot!(parses[0..=3].join("\n"));
}

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
fn math() {
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

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn parse_dna() {
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
        .parse()
        .unwrap();

    let input = "GATTACA";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn shared_nonterminal_failure() {
    let grammar = "
        <start> ::= <shortfail> | <longsuccess>
        <shortfail> ::= <char> 'never'
        <char> ::= 'a'
        <longsuccess> ::= <long2>
        <long2> ::= <long3>
        <long3> ::= <long4>
        <long4> ::= <char>
        ";

    let grammar = grammar.parse::<Grammar>().unwrap();

    let input = "a";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn swap_left_right_recursion() {
    let input = "aa a";

    let left_recursive: &str = "
        <conjunction> ::= <conjunction> <ws> <predicate> | <predicate>
        <predicate> ::= <string_null_one> | <special-string> '.'
        <string_null_one> ::= <string_null_two>
        <string_null_two> ::= <string_null_three>
        <string_null_three> ::= <string>
        <string> ::= <char_null> | <string> <char_null>
        <special-string> ::= <special-char> | <special-string> <special-char>
        <char_null> ::= <char>
        <char> ::= 'a'
        <special-char> ::= <char_null> | <whitespace>
        <whitespace> ::= ' '
        <ws> ::= ' ' | ' ' <ws>
        ";
    let parses: Vec<_> = left_recursive
        .parse::<Grammar>()
        .unwrap()
        .parse_input(input)
        .map(|a| a.to_string())
        .collect();
    assert_snapshot!(parses.join("\n"));

    let right_recursive = left_recursive.replace(
        // rewrite production from left- to right- recursive
        "<string> ::= <char_null> | <string> <char_null>",
        "<string> ::= <char_null> | <char_null> <string>",
    );
    let parses: Vec<_> = right_recursive
        .parse::<Grammar>()
        .unwrap()
        .parse_input(input)
        .map(|a| a.to_string())
        .collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn shared_nullable_nonterminal() {
    let grammar: &str = "
        <disjunction> ::= <predicate> | <disjunction> <or> <predicate>
        <predicate> ::= <char_null_one> | <special-string> '.'

        <char_null_one> ::= <char_null_two>
        <char_null_two> ::= <char_null_three>
        <char_null_three> ::= <char>

        <or> ::= <ws> 'or' <ws>
        <ws> ::= <whitespace> | ' ' <ws>
        <whitespace> ::= ' '

        <special-string> ::= <special-char> | <special-char> <special-string>
        <special-char> ::= <char> | <whitespace>
        <char> ::= 'a'
        ";

    let input = "a or a";

    let parses: Vec<_> = grammar
        .parse::<Grammar>()
        .unwrap()
        .parse_input(input)
        .map(|a| a.to_string())
        .collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn branching_and_overlapping_parse_trees() {
    let bnf = "
        <and> ::= <and> ' AND ' <terminal>
                | <and> ' ' <terminal>
                | <terminal>
        <terminal> ::= 'AND'
        ";
    let input = "AND AND AND AND AND";

    // 1. 'AND' <and> 'AND' <and> 'AND'
    // 2. 'AND' <and> 'AND' 'AND' 'AND'
    // 3. 'AND' 'AND' <and> 'AND' 'AND'
    // 4. 'AND' 'AND' 'AND' <and> 'AND'
    // 5. 'AND' 'AND' 'AND' 'AND' 'AND'
    let parses: Vec<_> = bnf
        .parse::<Grammar>()
        .unwrap()
        .parse_input(input)
        .map(|a| a.to_string())
        .collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn format_parse_tree() {
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
        .parse()
        .unwrap();

    let input = "GATTACA";
    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn mermaid_dna_parse_tree() {
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
        .parse()
        .unwrap();

    let input = "GATTACA";

    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    assert_snapshot!(mermaid.join("\n"));
}

#[test]
fn mermaid_math_parse_tree() {
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

    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    assert_snapshot!(mermaid.join("\n"));
}
