#![cfg(test)]

use bnf::Grammar;
use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
use rand::{SeedableRng, rngs::StdRng};
use std::sync::LazyLock;

#[derive(PartialEq, Debug, Clone)]
struct MetaBNF {
    bnf: String,
}

#[derive(PartialEq, Debug, Clone)]
struct MetaABNF {
    abnf: String,
}

impl From<String> for MetaBNF {
    fn from(bnf: String) -> Self {
        MetaBNF { bnf }
    }
}

impl From<String> for MetaABNF {
    fn from(abnf: String) -> Self {
        MetaABNF { abnf }
    }
}

// Modified version of BNF for BNF from
// https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form#Further_examples
const BNF_FOR_BNF: &str = std::include_str!("./fixtures/bnf.bnf");
const ABNF_FOR_BNF: &str = std::include_str!("./fixtures/bnf.abnf");

static GRAMMAR_FOR_BNF: LazyLock<Grammar> =
    LazyLock::new(|| BNF_FOR_BNF.parse().expect("Failed to parse BNF for BNF"));

static GRAMMAR_FOR_ABNF: LazyLock<Grammar> = LazyLock::new(|| {
    let grammar_abnf = ABNF_FOR_BNF.parse().expect("Failed to parse ABNF for BNF");

    assert_eq!(*GRAMMAR_FOR_BNF, grammar_abnf);

    grammar_abnf
});

fn generate_grammar_with_gen<T>(r#gen: &mut Gen, grammar: &Grammar) -> T
where
    T: From<String>,
{
    let seed: [u8; 32] = {
        let mut seed = [0u8; 32];
        for byte in seed.iter_mut() {
            *byte = Arbitrary::arbitrary(r#gen);
        }
        seed
    };

    let mut rng: StdRng = SeedableRng::from_seed(seed);
    let sentence = grammar.generate_seeded(&mut rng);

    sentence
        .map(T::from)
        .expect("Failed to generate a valid grammar")
}

impl Arbitrary for MetaBNF {
    fn arbitrary(r#gen: &mut Gen) -> Self {
        generate_grammar_with_gen(r#gen, &GRAMMAR_FOR_BNF)
    }
}

impl Arbitrary for MetaABNF {
    fn arbitrary(r#gen: &mut Gen) -> Self {
        generate_grammar_with_gen(r#gen, &GRAMMAR_FOR_ABNF)
    }
}

fn prop_bnf_grammar_from_str(meta: MetaBNF) -> TestResult {
    // parse a randomly generated grammar to a Grammar object
    let meta_grammar: Result<Grammar, _> = meta.bnf.parse();
    TestResult::from_bool(meta_grammar.is_ok())
}

#[test]
fn test_generated_grammars() {
    // Using a closure instead of a function pointer cast
    QuickCheck::new()
        .tests(1000)
        .quickcheck(prop_bnf_grammar_from_str as fn(MetaBNF) -> TestResult)
}

fn prop_abnf_grammar_from_str(meta: MetaABNF) -> TestResult {
    // parse a randomly generated grammar to a Grammar object
    let meta_grammar: Result<Grammar, _> = meta.abnf.parse();
    TestResult::from_bool(meta_grammar.is_ok())
}

#[test]
fn test_generated_grammars_abnf() {
    QuickCheck::new()
        .tests(1000)
        .quickcheck(prop_abnf_grammar_from_str as fn(MetaABNF) -> TestResult);
}
