#![cfg(test)]

use bnf::{Grammar, BNF, ABNF};
use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
use rand::{rngs::StdRng, SeedableRng};

#[derive(PartialEq, Debug, Clone)]
struct Meta {
    bnf: String,
}

// Modified version of BNF for BNF from
// https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Further_examples
const BNF_FOR_BNF: &str = std::include_str!("./fixtures/bnf.bnf");
const ABNF_FOR_BNF: &str = std::include_str!("./fixtures/abnf.abnf");

impl Arbitrary for Meta {
    fn arbitrary(gen: &mut Gen) -> Meta {
        // Generate Grammar object from grammar for BNF grammars
        let grammar_bnf: Result<Grammar, _> = Grammar::parse_from::<BNF>(BNF_FOR_BNF);
        assert!(grammar_bnf.is_ok(), "{grammar_bnf:?} should be Ok");

        let grammar_abnf: Result<Grammar, _> = Grammar::parse_from::<ABNF>(ABNF_FOR_BNF);
        assert!(grammar_abnf.is_ok(), "{grammar_abnf:?} should be Ok");

        assert_eq!(grammar_bnf, grammar_abnf);

        // generate a random valid grammar from the above
        // using an arbitrary seed
        let seed: [u8; 32] = {
            let mut seed = [0u8; 32];

            for byte in seed.iter_mut() {
                *byte = Arbitrary::arbitrary(gen);
            }

            seed
        };

        let mut rng: StdRng = SeedableRng::from_seed(seed);
        let sentence = grammar_bnf.unwrap().generate_seeded(&mut rng);

        match sentence {
            Err(e) => {
                panic!("Unexpected state {e:?} -- seed {seed:?}")
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
