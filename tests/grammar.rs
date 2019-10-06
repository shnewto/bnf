extern crate bnf;
extern crate quickcheck;
extern crate rand;

use bnf::Error;
use bnf::Grammar;
use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
use rand::{SeedableRng, StdRng};

#[derive(PartialEq, Debug, Clone)]
struct Meta {
    bnf: String,
}

// Modified version of BNF for BNF from
// https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Further_examples
const BNF_FOR_BNF: &str = "
        <syntax>         ::= <rule> | <rule> <syntax>
        <rule>           ::= <opt-whitespace> \"<\" <rule-name> \">\"
                            <opt-whitespace> \"::=\" <opt-whitespace>
                            <expression> <line-end>
        <opt-whitespace> ::= \"\" | \" \" <opt-whitespace>
        <expression>     ::= <list> | <list> <opt-whitespace> \"|\"
                            <opt-whitespace> <expression>
        <line-end>       ::= <opt-whitespace> <EOL>
        <list>           ::= <term> | <term> <opt-whitespace> <list>
        <term>           ::= <literal> | \"<\" <rule-name> \">\"
        <literal>        ::= '\"' <text1> '\"' | \"'\" <text2> \"'\"
        <text1>          ::= \"\" | <character1> <text1>
        <text2>          ::= \"\" | <character2> <text2>
        <character>      ::= <letter> | <digit> | <symbol>
        <letter>         ::= \"A\" | \"B\" | \"C\" | \"D\" | \"E\" | \"F\"
                            | \"G\" | \"H\" | \"I\" | \"J\" | \"K\" | \"L\"
                            | \"M\" | \"N\" | \"O\" | \"P\" | \"Q\" | \"R\"
                            | \"S\" | \"T\" | \"U\" | \"V\" | \"W\" | \"X\"
                            | \"Y\" | \"Z\" | \"a\" | \"b\" | \"c\" | \"d\"
                            | \"e\" | \"f\" | \"g\" | \"h\" | \"i\" | \"j\"
                            | \"k\" | \"l\" | \"m\" | \"n\" | \"o\" | \"p\"
                            | \"q\" | \"r\" | \"s\" | \"t\" | \"u\" | \"v\"
                            | \"w\" | \"x\" | \"y\" | \"z\"
        <digit>          ::= \"0\" | \"1\" | \"2\" | \"3\" | \"4\" | \"5\"
                            | \"6\" | \"7\" | \"8\" | \"9\"
        <symbol>         ::=  \"|\" | \" \" | \"-\" | \"!\" | \"#\" | \"$\"
                            | \"%\" | \"&\" | \"(\" | \")\" | \"*\" | \"+\"
                            | \",\" | \"-\" | \".\" | \"/\" | \":\" | \";\"
                            |\">\" | \"=\" | \"<\" | \"?\" | \"@\" | \"[\"
                            | \"\\\" | \"]\" | \"^\" | \"_\" | \"`\"
                            | \"{{\" | \"}}\" | \"~\"
        <character1>     ::= <character> | \"'\"
        <character2>     ::= <character> | '\"'
        <rule-name>      ::= <letter> | <rule-name> <rule-char>
        <rule-char>      ::= <letter> | <digit> | \"-\"
        <EOL>            ::= \"\n\"";

impl Arbitrary for Meta {
    fn arbitrary<G: Gen>(g: &mut G) -> Meta {
        // Generate Grammar object from grammar for BNF grammars
        let grammar = Grammar::from_str(BNF_FOR_BNF);
        assert!(grammar.is_ok(), "{:?} should be Ok", grammar);

        // generate a random valid grammar from the above
        let seed: Vec<_> = Arbitrary::arbitrary(g);
        let mut rng: StdRng = SeedableRng::from_seed(&seed[..]);
        let sentence = grammar.unwrap().generate_seeded(&mut rng);

        match sentence {
            Err(e) => {
                match e {
                    // shouldn't cause parsing to fail if random generation
                    // recurses too far
                    Error::RecursionLimit(_) => Meta {
                        bnf: String::from(
                            "<if-recursion-limit-reached> ::= \"parse shouldn't fail\"",
                        ),
                    },
                    _ => panic!("Unexpected state {:?} -- seed {:?}", e, seed),
                }
            }
            Ok(s) => Meta { bnf: s },
        }
    }
}

fn prop_grammar_from_str(meta: Meta) -> TestResult {
    // parse a randomly generated grammar to a Grammar object
    let meta_grammar = Grammar::from_str(&meta.bnf);
    TestResult::from_bool(meta_grammar.is_ok())
}

#[test]
fn test_generated_grammars() {
    QuickCheck::new().quickcheck(prop_grammar_from_str as fn(Meta) -> TestResult)
}
