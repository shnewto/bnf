use bnf::Error;
use bnf::Grammar;
use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
use rand::{rngs::StdRng, SeedableRng};

#[derive(PartialEq, Debug, Clone)]
struct Meta {
    bnf: String,
}

// Modified version of BNF for BNF from
// https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Further_examples
const BNF_FOR_BNF: &str = std::include_str!("./fixtures/bnf.bnf");

impl Arbitrary for Meta {
    fn arbitrary(_: &mut Gen) -> Meta {
        // Generate Grammar object from grammar for BNF grammars
        let grammar: Result<Grammar, _> = BNF_FOR_BNF.parse();
        assert!(grammar.is_ok(), "{grammar:?} should be Ok");

        // generate a random valid grammar from the above
        let seed: [u8; 32] = [0; 32];
        let mut rng: StdRng = SeedableRng::from_seed(seed);
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
                    _ => panic!("Unexpected state {e:?} -- seed {seed:?}"),
                }
            }
            Ok(s) => Meta { bnf: s },
        }
    }
}

fn prop_grammar_from_str(meta: Meta) -> TestResult {
    // parse a randomly generated grammar to a Grammar object
    let meta_grammar: Result<Grammar, _> = meta.bnf.parse();
    TestResult::from_bool(meta_grammar.is_ok())
}

#[test]
fn test_generated_grammars() {
    QuickCheck::new().quickcheck(prop_grammar_from_str as fn(Meta) -> TestResult)
}
