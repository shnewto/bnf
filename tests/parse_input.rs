#![cfg(test)]
#![allow(deprecated)]

use bnf::{Grammar, ParseTree, ParseTreeNode, escape_mermaid_label};
use insta::assert_snapshot;
use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
use rand::SeedableRng;
use std::fmt;
use std::sync::LazyLock;

#[test]
fn undefined_prod() {
    // Grammar references <b> but only defines <a>; validation should fail
    let grammar: Grammar = "
        <start> ::= <a> | <b>
        <a> ::= 'a'
        "
    .parse()
    .unwrap();

    let parser_result = grammar.build_parser();
    assert!(
        parser_result.is_err(),
        "Parser should fail when grammar has undefined nonterminals"
    );
}

#[test]
fn undefined_prod_deprecated_parses() {
    // Deprecated parse_input skips validation: grammar has undefined <b> but still
    // parses via the defined <a> branch.
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
        <base> ::= 'A' | 'C' | 'G' | 'T'"
        .parse()
        .unwrap();

    let input = "GATTACA";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn dna_right_recursive() {
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
        .parse()
        .unwrap();

    let input = "GATTACA";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn dna_annotated_grammar_parses_input() {
    // Same DNA grammar as dna_right_recursive but with BNF comments throughout.
    // Comments are stripped; parsing "GATTACA" yields the same parse trees.
    let grammar: Grammar = "; the building blocks of life!
<dna> ::= <base> | <base> <dna>
<base> ::= 'A' | 'C' | 'G' | 'T' ;(Adenine, Cytosine, Guanine, and Thymine)
; the end 📖"
        .parse()
        .unwrap();

    let input = "GATTACA";
    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn ambiguous() {
    let grammar: Grammar = "<start> ::= <a> | <b>
        <a> ::= 'END'
        <b> ::= 'END'"
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
    assert_snapshot!(parses.get(0..=3).unwrap().join("\n"));
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
    let grammar: Grammar = "<start> ::= 'hi' <empty>
        <empty> ::= ''"
        .parse()
        .unwrap();

    let input = "hi";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn empty() {
    let grammar: Grammar = "<start> ::= ''".parse().unwrap();

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
    assert_snapshot!(parses.get(0..=3).unwrap().join("\n"));
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
    assert_snapshot!(parses.get(0..=3).unwrap().join("\n"));
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
            <add> ::= '+' | '-'
            <mult> ::= '*' | '/'
            <factor> ::= '(' <sum> ')'
            <factor> ::= <number>
            <number> ::= <digit> <number>
            <number> ::= <digit>
            <digit> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
    .parse()
    .unwrap();

    let input = "1+(2*3-4)";

    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn parse_dna() {
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
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

    let left_recursive = "
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
    let grammar = "
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
        <base> ::= 'A' | 'C' | 'G' | 'T'"
        .parse()
        .unwrap();

    let input = "GATTACA";
    let parses: Vec<_> = grammar.parse_input(input).map(|a| a.to_string()).collect();
    assert_snapshot!(parses.join("\n"));
}

#[test]
fn mermaid_dna_parse_tree() {
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
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
            <add> ::= '+' | '-'
            <mult> ::= '*' | '/'
            <factor> ::= '(' <sum> ')'
            <factor> ::= <number>
            <number> ::= <digit> <number>
            <number> ::= <digit>
            <digit> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
    .parse()
    .unwrap();

    let input = "1+(2*3-4)";

    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    assert_snapshot!(mermaid.join("\n"));
}

#[test]
fn mermaid_via_build_parser() {
    // Recommended API: build_parser().unwrap().parse_input(...) instead of deprecated parse_input.
    let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
        .parse()
        .unwrap();
    let parser = grammar.build_parser().unwrap();
    let input = "GATTACA";
    let mermaid: Vec<_> = parser
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    assert!(!mermaid.is_empty());
    let output = mermaid.join("\n");
    assert!(output.starts_with("flowchart TD"));
    assert!(output.contains("-->"));
}

// --- Mermaid entity-code escaping: labels with ", ], [, \, #, ;, newlines ---
// Node labels are escaped with Mermaid entity codes so flowchart syntax is valid
// (see https://mermaid.js.org/syntax/flowchart.html#entity-codes-to-escape-characters).

#[test]
fn mermaid_punctuation_double_quote_terminal() {
    // Terminal is the double-quote character; escaped as #34; in label.
    let grammar: Grammar = r#"<q> ::= '"'
        "#
    .parse()
    .unwrap();
    let input = "\"";
    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    let output = mermaid.join("\n");
    assert_snapshot!(output);
}

#[test]
fn mermaid_punctuation_closing_bracket_terminal() {
    // Terminal ']' escaped as #93; in label.
    let grammar: Grammar = "<b> ::= ']'
        "
    .parse()
    .unwrap();
    let input = "]";
    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    let output = mermaid.join("\n");
    assert_snapshot!(output);
}

#[test]
fn mermaid_punctuation_opening_bracket_terminal() {
    // Terminal '[' escaped as #91; in label.
    let grammar: Grammar = "<b> ::= '['
        "
    .parse()
    .unwrap();
    let input = "[";
    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    let output = mermaid.join("\n");
    assert_snapshot!(output);
}

#[test]
fn mermaid_punctuation_backslash_terminal() {
    // Terminal '\' escaped as #92; in label.
    let grammar: Grammar = r#"<b> ::= '\\'"#.parse().unwrap();
    let input = "\\";
    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    let output = mermaid.join("\n");
    assert_snapshot!(output);
}

#[test]
fn mermaid_punctuation_slash_and_angle_brackets() {
    // Slash and angle brackets don't require escaping; '/' in label.
    let grammar: Grammar = "<expr> ::= '/'
        "
    .parse()
    .unwrap();
    let input = "/";
    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    let output = mermaid.join("\n");
    assert_snapshot!(output);
}

/// List-of-strings grammar: parses ["foo", "bar", "baz"] (a list of quoted strings).
/// Uses special characters [ ] " , so Mermaid output escapes them with entity codes.
#[test]
fn mermaid_silly_syntax_salad() {
    // string terminals are single-quoted so the inner " is literal: '"foo"' etc.
    let grammar: Grammar = r#"
        <list> ::= '[' <items> ']'
        <items> ::= <string> ',' <items> | <string>
        <string> ::= '"foo"' | '"bar"' | '"baz"'
        "#
    .parse()
    .unwrap();
    let input = "[\"foo\",\"bar\",\"baz\"]";
    let parses: Vec<_> = grammar.parse_input(input).collect();
    assert!(!parses.is_empty(), "grammar should parse list of strings");
    let mermaid: Vec<_> = parses
        .into_iter()
        .map(|a| a.mermaid().to_string())
        .collect();
    let output = mermaid.join("\n");
    assert_snapshot!(output);
}

#[test]
fn mermaid_entity_codes_hash_and_semicolon() {
    // Terminals '#' and ';' escaped as #35; and #59; in labels.
    let grammar: Grammar = "<h> ::= '#' | ';'
        "
    .parse()
    .unwrap();
    for input in ["#", ";"] {
        let mermaid: Vec<_> = grammar
            .parse_input(input)
            .map(|a| a.mermaid().to_string())
            .collect();
        let output = mermaid.join("\n");
        assert!(
            output.contains("#35;") || output.contains("#59;"),
            "output should escape # or ;"
        );
        for line in output.lines() {
            if line.contains("-->") {
                assert_eq!(
                    line.matches('"').count(),
                    4,
                    "balanced quotes on line: {line:?}"
                );
            }
        }
    }
}

#[test]
fn mermaid_entity_codes_newline_in_label() {
    // Newline in terminal escaped as #10; so flowchart stays one statement per line.
    let grammar: Grammar = "<nl> ::= '\n'
        "
    .parse()
    .unwrap();
    let input = "\n";
    let mermaid: Vec<_> = grammar
        .parse_input(input)
        .map(|a| a.mermaid().to_string())
        .collect();
    let output = mermaid.join("\n");
    assert!(output.contains("#10;"), "newline should be escaped as #10;");
    assert!(
        !output.contains("\n\n"),
        "no double newline from raw newline in label"
    );
}

#[test]
fn mermaid_escape_mermaid_label_public_api() {
    // Public API: escape_mermaid_label produces valid Mermaid entity codes.
    assert_eq!(escape_mermaid_label("a\"b"), "a#34;b");
    assert_eq!(escape_mermaid_label("["), "#91;");
    assert_eq!(escape_mermaid_label("]"), "#93;");
    assert_eq!(escape_mermaid_label("\\"), "#92;");
    assert_eq!(escape_mermaid_label("#"), "#35;");
    assert_eq!(escape_mermaid_label(";"), "#59;");
    assert_eq!(escape_mermaid_label("<"), "#60;");
    assert_eq!(escape_mermaid_label(">"), "#62;");
    assert_eq!(escape_mermaid_label("&"), "#38;");
    assert_eq!(escape_mermaid_label("plain"), "plain");
}

/// Asserts that generated Mermaid has balanced double-quotes in node labels so
/// the flowchart is parseable (labels escaped with entity codes).
#[test]
fn mermaid_output_safe_for_special_chars() {
    let grammar: Grammar = r#"<q> ::= '"'
        <b> ::= ']' | '['
        <s> ::= '\\'
        "#
    .parse()
    .unwrap();

    for input in ["\"", "]", "[", "\\"] {
        let mermaid: Vec<_> = grammar
            .parse_input(input)
            .map(|a| a.mermaid().to_string())
            .collect();
        let output = mermaid.join("\n");
        for line in output.lines() {
            if line.is_empty() || line == "flowchart TD" {
                continue;
            }
            // Each edge line: N["..."] --> M["..."] - exactly 4 quotes (two node wrappers).
            let quote_count = line.matches('"').count();
            assert_eq!(
                quote_count, 4,
                "Line must have 4 quotes (balanced node labels). input={:?} line={:?} count={}",
                input, line, quote_count
            );
        }
    }
}

// -----------------------------------------------------------------------------
// Property tests: parse-tree invariants, API parity, Mermaid output
// -----------------------------------------------------------------------------

/// Terminating grammars that produce short sentences to avoid deep parse trees and stack overflow.
static TERMINATING_GRAMMARS: LazyLock<Vec<Grammar>> = LazyLock::new(|| {
    vec![
        "<x> ::= 'a' | 'b' | 'c'"
            .parse()
            .expect("single-char grammar"),
        "<ab> ::= 'a' 'b' | 'a' <ab> 'b'"
            .parse()
            .expect("a^n b^n grammar"),
        "<list> ::= <digit> | <digit> ',' <list>\n<digit> ::= '0' | '1' | '2'"
            .parse()
            .expect("digit list grammar"),
    ]
});

/// A grammar and an input string that parses with that grammar (sentence generated from the grammar).
#[derive(Clone)]
struct ParsableInput {
    grammar: Grammar,
    input: String,
}

impl fmt::Debug for ParsableInput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ParsableInput(grammar, {:?})", self.input)
    }
}

impl Arbitrary for ParsableInput {
    fn arbitrary(g: &mut Gen) -> Self {
        let grammars = LazyLock::force(&TERMINATING_GRAMMARS);
        let idx = usize::arbitrary(g) % grammars.len();
        let grammar = grammars.get(idx).expect("non-empty").clone();
        let seed = u64::arbitrary(g);
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut input = grammar
            .generate_seeded(&mut rng)
            .expect("grammar must terminate");
        if input.len() > 50 {
            input.truncate(50);
        }
        ParsableInput { grammar, input }
    }
}

fn collect_terminals(tree: &ParseTree<'_>) -> String {
    let mut s = String::new();
    for node in tree.rhs_iter() {
        match node {
            ParseTreeNode::Terminal(t) => s.push_str(t),
            ParseTreeNode::Nonterminal(nt) => s.push_str(&collect_terminals(nt)),
        }
    }
    s
}

fn prop_parse_tree_terminals_equal_input(p: ParsableInput) -> TestResult {
    let parser = match p.grammar.build_parser() {
        Ok(parser) => parser,
        Err(e) => return TestResult::error(format!("build_parser failed: {e}")),
    };
    let parses: Vec<_> = parser.parse_input(&p.input).collect();
    if parses.is_empty() {
        return TestResult::error(format!(
            "expected at least one parse for input {:?}",
            p.input
        ));
    }
    for tree in &parses {
        let terminals = collect_terminals(tree);
        if terminals != p.input {
            return TestResult::error(format!("terminals {:?} != input {:?}", terminals, p.input));
        }
    }
    TestResult::passed()
}

fn prop_parse_input_build_parser_parity(p: ParsableInput) -> TestResult {
    let deprecated: Vec<_> = p.grammar.parse_input(&p.input).collect();
    let parser = match p.grammar.build_parser() {
        Ok(parser) => parser,
        Err(e) => return TestResult::error(format!("build_parser failed: {e}")),
    };
    let recommended: Vec<_> = parser.parse_input(&p.input).collect();
    if deprecated != recommended {
        return TestResult::error(format!(
            "API parity: deprecated len {} != recommended len {}",
            deprecated.len(),
            recommended.len()
        ));
    }
    TestResult::passed()
}

#[test]
fn parse_prop_terminals_equal_input() {
    QuickCheck::new()
        .tests(200)
        .r#gen(Gen::new(16))
        .quickcheck(prop_parse_tree_terminals_equal_input as fn(ParsableInput) -> TestResult)
}

#[test]
fn parse_prop_build_parser_parity() {
    QuickCheck::new()
        .tests(200)
        .r#gen(Gen::new(16))
        .quickcheck(prop_parse_input_build_parser_parity as fn(ParsableInput) -> TestResult)
}

/// Content suitable for a single-quoted BNF terminal (no unescaped `'`). May contain Mermaid-special chars.
#[derive(Clone)]
struct MermaidLabelContent(String);

impl fmt::Debug for MermaidLabelContent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MermaidLabelContent({:?})", self.0)
    }
}

impl Arbitrary for MermaidLabelContent {
    fn arbitrary(g: &mut Gen) -> Self {
        let s: String = String::arbitrary(g);
        MermaidLabelContent(s.replace('\'', "_"))
    }
}

fn count_parse_tree_edges(tree: &ParseTree<'_>) -> usize {
    let mut n = tree.rhs_iter().count();
    for node in tree.rhs_iter() {
        if let ParseTreeNode::Nonterminal(nt) = node {
            n += count_parse_tree_edges(nt);
        }
    }
    n
}

fn assert_mermaid_edge_lines_balanced(mermaid: &str) -> Result<(), String> {
    for line in mermaid.lines() {
        if line.contains("-->") {
            let quote_count = line.matches('"').count();
            if quote_count != 4 {
                return Err(format!(
                    "edge line must have 4 quotes (balanced node labels), got {}: {:?}",
                    quote_count, line
                ));
            }
        }
    }
    Ok(())
}

fn count_mermaid_edges(mermaid: &str) -> usize {
    mermaid.lines().filter(|l| l.contains("-->")).count()
}

const MERMAID_RAW_SPECIALS: &[char] = &['"', '[', ']', '\\', '<', '>', '&', '\n', '\r'];

fn assert_mermaid_labels_no_raw_specials(mermaid: &str) -> Result<(), String> {
    for segment in mermaid.split("[\"") {
        if let Some(label) = segment.split("\"]").next()
            && label != segment
        {
            for &bad in MERMAID_RAW_SPECIALS {
                if label.contains(bad) {
                    return Err(format!("raw special {:?} in label {:?}", bad, label));
                }
            }
        }
    }
    Ok(())
}

fn unescape_mermaid_entity_codes(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut it = s.chars().peekable();
    while let Some(c) = it.next() {
        if c == '#' {
            let mut digits = String::new();
            while it.peek().copied().is_some_and(|d| d.is_ascii_digit()) {
                digits.push(it.next().unwrap());
            }
            if it.peek() == Some(&';') && !digits.is_empty() {
                it.next();
                if let Ok(n) = digits.parse::<u32>()
                    && let Some(ch) = std::char::from_u32(n)
                {
                    out.push(ch);
                    continue;
                }
            }
            out.push('#');
            out.push_str(&digits);
        } else {
            out.push(c);
        }
    }
    out
}

fn grammar_single_node(content: &str) -> String {
    format!("<root> ::= '{}'", content)
}

fn prop_mermaid_single_node_well_formed(content: MermaidLabelContent) -> TestResult {
    let s = content.0;
    let grammar_src = grammar_single_node(&s);
    let grammar: Grammar = match grammar_src.parse() {
        Ok(g) => g,
        Err(e) => {
            return TestResult::error(format!("grammar parse failed: {grammar_src:?} -> {e}"));
        }
    };
    let parser = match grammar.build_parser() {
        Ok(p) => p,
        Err(e) => return TestResult::error(format!("build_parser failed: {e}")),
    };
    let parses: Vec<_> = parser.parse_input(&s).collect();
    if parses.is_empty() {
        return TestResult::error(format!("expected at least one parse for input {s:?}"));
    }
    for tree in &parses {
        let mermaid = tree.mermaid().to_string();
        if let Err(e) = assert_mermaid_edge_lines_balanced(&mermaid) {
            return TestResult::error(e);
        }
        let tree_edges = count_parse_tree_edges(tree);
        let mermaid_edges = count_mermaid_edges(&mermaid);
        if tree_edges != mermaid_edges {
            return TestResult::error(format!(
                "edge count: tree {} != mermaid {}",
                tree_edges, mermaid_edges
            ));
        }
        if let Err(e) = assert_mermaid_labels_no_raw_specials(&mermaid) {
            return TestResult::error(e);
        }
    }
    TestResult::passed()
}

fn prop_escape_mermaid_round_trip(content: MermaidLabelContent) -> TestResult {
    let s = &content.0;
    let escaped = escape_mermaid_label(s);
    let round = unescape_mermaid_entity_codes(&escaped);
    if *s != round {
        return TestResult::error(format!(
            "round-trip: original {:?} != unescape(escape(...)) {:?}",
            s, round
        ));
    }
    TestResult::passed()
}

#[test]
fn mermaid_prop_arbitrary_labels_well_formed() {
    QuickCheck::new()
        .tests(500)
        .r#gen(Gen::new(20))
        .quickcheck(prop_mermaid_single_node_well_formed as fn(MermaidLabelContent) -> TestResult)
}

#[test]
fn mermaid_prop_escape_round_trip() {
    QuickCheck::new()
        .tests(500)
        .r#gen(Gen::new(20))
        .quickcheck(prop_escape_mermaid_round_trip as fn(MermaidLabelContent) -> TestResult)
}
