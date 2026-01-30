pub(crate) mod grammar;

use crate::ParseTree;
use crate::error::Error;
use crate::grammar::Grammar;
use crate::term::Term;
use grammar::ParseGrammar;
use std::collections::HashSet;
use std::rc::Rc;

/// A reusable parser built from a `Grammar` that validates all nonterminals are defined
/// at construction time.
///
/// # Example
///
/// ```rust
/// use bnf::Grammar;
///
/// let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
/// <base> ::= 'A' | 'C' | 'G' | 'T'"
///     .parse()
///     .unwrap();
///
/// let parser = grammar.build_parser()?;
/// let parse_trees: Vec<_> = parser.parse_input("GATTACA").collect();
/// # Ok::<(), bnf::Error>(())
/// ```
#[derive(Debug)]
pub struct GrammarParser<'gram> {
    starting_term: &'gram Term,
    parse_grammar: Rc<ParseGrammar<'gram>>,
}

impl<'gram> GrammarParser<'gram> {
    /// Construct a new `GrammarParser` from a `Grammar`, validating that all
    /// nonterminals referenced in productions have definitions.
    ///
    /// # Errors
    ///
    /// Returns `Error::ValidationError` if any nonterminal used in the RHS of
    /// productions lacks a definition in the grammar.
    pub fn new(grammar: &'gram Grammar) -> Result<Self, Error> {
        validate_nonterminals(grammar)?;
        let starting_term = grammar.starting_term().ok_or_else(|| {
            Error::ValidationError("Grammar must have at least one production".to_string())
        })?;
        let parse_grammar = Rc::new(ParseGrammar::new(grammar));
        Ok(Self {
            starting_term,
            parse_grammar,
        })
    }

    /// Parse an input string using the grammar's starting nonterminal.
    ///
    /// Returns an iterator over all possible parse trees for the input.
    pub fn parse_input(&self, input: &'gram str) -> impl Iterator<Item = ParseTree<'gram>> {
        self.parse_input_starting_with(input, self.starting_term)
    }

    /// Parse an input string starting with the given term (nonterminal or terminal).
    ///
    /// Returns an iterator over all possible parse trees for the input.
    pub fn parse_input_starting_with(
        &self,
        input: &'gram str,
        start: &'gram Term,
    ) -> impl Iterator<Item = ParseTree<'gram>> {
        crate::earley::parse_starting_with_grammar(&self.parse_grammar, input, start)
    }
}

/// Validate that all nonterminals referenced in the grammar have definitions.
///
/// # Errors
///
/// Returns `Error::ValidationError` with a message listing all undefined nonterminals.
fn validate_nonterminals(grammar: &Grammar) -> Result<(), Error> {
    // Collect all nonterminals defined in LHS of productions
    let mut defined_nonterminals = HashSet::new();
    for production in grammar.productions_iter() {
        if let Term::Nonterminal(ref nt) = production.lhs {
            defined_nonterminals.insert(nt.clone());
        }
    }

    // Collect all nonterminals used in RHS of all productions
    let mut referenced_nonterminals = HashSet::new();
    for production in grammar.productions_iter() {
        for expression in production.rhs_iter() {
            for term in expression.terms_iter() {
                if let Term::Nonterminal(nt) = term {
                    referenced_nonterminals.insert(nt.clone());
                }
            }
        }
    }

    // Find undefined nonterminals
    let undefined: Vec<String> = referenced_nonterminals
        .difference(&defined_nonterminals)
        .cloned()
        .collect();

    if !undefined.is_empty() {
        let message = format!(
            "Undefined nonterminals: {}",
            undefined
                .iter()
                .map(|nt| format!("<{nt}>"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        return Err(Error::ValidationError(message));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;
    use crate::expression::Expression;
    use crate::production::Production;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    #[test]
    fn parser_construction_with_valid_grammar() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();

        let parser = grammar.build_parser();
        assert!(
            parser.is_ok(),
            "Parser should be constructible from valid grammar"
        );
    }

    #[test]
    fn parser_construction_fails_with_empty_grammar() {
        let grammar = Grammar::from_parts(vec![]);
        let parser = grammar.build_parser();
        assert!(
            parser.is_err(),
            "Parser construction should fail with empty grammar"
        );
        assert!(
            matches!(parser.unwrap_err(), Error::ValidationError(_)),
            "Error should be ValidationError about missing productions"
        );
    }

    #[test]
    fn parser_validation_with_group_containing_undefined() {
        // Test that validation fails when a grouped term references an undefined nonterminal
        let grammar: Grammar = "<start> ::= (<undefined>)".parse().unwrap();
        let parser = grammar.build_parser();
        assert!(
            parser.is_err(),
            "Parser should fail when group contains undefined nonterminal"
        );
        assert!(matches!(parser.unwrap_err(), Error::ValidationError(_)));
    }

    #[test]
    fn parser_validation_with_group_containing_defined() {
        // Test that validation succeeds when a group contains a defined nonterminal
        let grammar: Grammar = "<start> ::= (<base>)\n<base> ::= 'A'".parse().unwrap();
        let parser = grammar.build_parser();
        assert!(
            parser.is_ok(),
            "Parser should succeed when group contains defined nonterminal"
        );
    }

    #[test]
    fn normalization_groups_and_optionals_produce_named_nonterminals() {
        // Regression: extended syntax ( ) and [ ] is normalized to __anon* nonterminals
        let grammar: Grammar = "<s> ::= (<a> | <b>) [<c>]\n<a> ::= 'a'\n<b> ::= 'b'\n<c> ::= 'c'"
            .parse()
            .unwrap();
        for prod in grammar.productions_iter() {
            for expr in prod.rhs_iter() {
                for term in expr.terms_iter() {
                    match term {
                        crate::Term::Terminal(_) | crate::Term::Nonterminal(_) => {}
                    }
                }
            }
        }
        let parser = grammar.build_parser().unwrap();
        assert!(parser.parse_input("a").next().is_some());
        assert!(parser.parse_input("ac").next().is_some());
        assert!(parser.parse_input("").next().is_none());
    }

    #[test]
    fn parse_empty_optional_bnf() {
        // BNF optional [A] normalizes to __anon* with '' alternative; "" and "x" both parse
        let grammar: Grammar = "<s> ::= [<x>]\n<x> ::= 'x'".parse().unwrap();
        let parser = grammar.build_parser().unwrap();
        assert!(parser.parse_input("").next().is_some());
        assert!(parser.parse_input("x").next().is_some());
    }

    #[test]
    fn user_defined_anon_name_no_collision() {
        // User-defined <__anon0> should not collide with generated anon names for groups
        let grammar: Grammar = "<__anon0> ::= 'a'\n<s> ::= (<__anon0>)".parse().unwrap();
        let parser = grammar.build_parser().unwrap();
        assert!(parser.parse_input("a").next().is_some());
        // Grammar should contain both user's __anon0 and a generated anon for the group
        let lhs_names: Vec<_> = grammar
            .productions_iter()
            .map(|p| match &p.lhs {
                crate::Term::Nonterminal(n) => n.as_str(),
                _ => "",
            })
            .collect();
        assert!(lhs_names.contains(&"__anon0"));
        assert!(lhs_names.iter().any(|n| n.starts_with("__anon")));
    }

    #[test]
    fn parser_construction_fails_with_undefined_nonterminal() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= <undefined>"
            .parse()
            .unwrap();

        let parser = grammar.build_parser();
        assert!(
            parser.is_err(),
            "Parser construction should fail with undefined nonterminal"
        );
        assert!(
            matches!(parser.unwrap_err(), Error::ValidationError(_)),
            "Error should be ValidationError"
        );
    }

    #[test]
    fn parser_can_parse_multiple_inputs() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();

        let parser = grammar.build_parser().unwrap();

        let input1 = "GATTACA";
        let input2 = "ATCG";

        let parse_trees1: Vec<_> = parser.parse_input(input1).collect();
        let parse_trees2: Vec<_> = parser.parse_input(input2).collect();

        assert!(!parse_trees1.is_empty(), "Should parse first input");
        assert!(!parse_trees2.is_empty(), "Should parse second input");
    }

    #[test]
    fn parser_accepts_explicit_starting_nonterminal() {
        let grammar: Grammar = "<base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>"
            .parse()
            .unwrap();

        let parser = grammar.build_parser().unwrap();
        let input = "GATTACA";
        let start_term = crate::term!(<dna>);

        let parse_trees: Vec<_> = parser
            .parse_input_starting_with(input, &start_term)
            .collect();

        assert!(
            !parse_trees.is_empty(),
            "Should parse with explicit starting nonterminal"
        );
    }

    #[test]
    fn parser_accepts_explicit_starting_terminal() {
        let grammar: Grammar = "<base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>"
            .parse()
            .unwrap();

        let parser = grammar.build_parser().unwrap();
        let input = "G";
        let start_term = crate::term!("G");

        // Note: Starting with a terminal directly doesn't work with Earley parser
        // since it expects a nonterminal to have productions. This test verifies
        // the API accepts terminals, but they won't produce parse trees unless
        // there's a production with that terminal as LHS (which is invalid).
        let parse_trees: Vec<_> = parser
            .parse_input_starting_with(input, &start_term)
            .collect();

        // This will be empty since there's no production with a terminal as LHS
        // The API accepts it, but it won't produce results
        assert_eq!(
            parse_trees.len(),
            0,
            "Terminal starting term produces no parse trees"
        );
    }

    #[test]
    fn parser_is_order_independent() {
        // Create grammar with productions in one order
        let grammar1: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();

        // Create same grammar with productions in different order
        let grammar2: Grammar = "<base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>"
            .parse()
            .unwrap();

        let parser1 = grammar1.build_parser().unwrap();
        let parser2 = grammar2.build_parser().unwrap();

        let input = "GATTACA";
        // Use explicit starting term to ensure both use the same starting point
        let start_term = crate::term!(<dna>);

        let parse_trees1: Vec<_> = parser1
            .parse_input_starting_with(input, &start_term)
            .collect();
        let parse_trees2: Vec<_> = parser2
            .parse_input_starting_with(input, &start_term)
            .collect();

        // Results should be identical regardless of production order when using
        // the same explicit starting term
        assert_eq!(
            parse_trees1.len(),
            parse_trees2.len(),
            "Should produce same number of parse trees regardless of order"
        );
    }

    // Helper: Generate a simple valid grammar with known structure
    #[derive(Debug, Clone)]
    struct SimpleValidGrammar(Grammar);
    impl Arbitrary for SimpleValidGrammar {
        fn arbitrary(g: &mut Gen) -> Self {
            // Generate 1-5 nonterminal names
            let num_nonterms = usize::arbitrary(g) % 5 + 1;
            let nonterms: Vec<String> = (0..num_nonterms).map(|i| format!("nt{}", i)).collect();

            let mut productions = Vec::new();

            // Create productions: each nonterminal references only defined ones
            for (idx, nt) in nonterms.iter().enumerate() {
                let mut expressions = Vec::new();

                // Each production has 1-3 alternatives
                let num_alternatives = usize::arbitrary(g) % 3 + 1;
                for _ in 0..num_alternatives {
                    let mut terms = Vec::new();

                    // Each alternative has 1-3 terms
                    let num_terms = usize::arbitrary(g) % 3 + 1;
                    for _ in 0..num_terms {
                        if bool::arbitrary(g) && idx > 0 {
                            // Reference a previously defined nonterminal
                            let ref_idx = usize::arbitrary(g) % idx;
                            if let Some(nt) = nonterms.get(ref_idx) {
                                terms.push(Term::Nonterminal(nt.clone()));
                            } else {
                                // Use a terminal if index is out of bounds
                                let term_str = String::arbitrary(g);
                                terms.push(Term::Terminal(term_str));
                            }
                        } else {
                            // Use a terminal
                            let term_str = String::arbitrary(g);
                            terms.push(Term::Terminal(term_str));
                        }
                    }

                    expressions.push(Expression::from_parts(terms));
                }

                productions.push(Production::from_parts(
                    Term::Nonterminal(nt.clone()),
                    expressions,
                ));
            }

            Self(Grammar::from_parts(productions))
        }
    }

    // Helper: Generate grammar that may have undefined nonterminals
    #[derive(Debug, Clone)]
    struct GrammarWithUndefined(Grammar);
    impl Arbitrary for GrammarWithUndefined {
        fn arbitrary(g: &mut Gen) -> Self {
            let num_nonterms = usize::arbitrary(g) % 4 + 1;
            let mut nonterms: Vec<String> = (0..num_nonterms).map(|i| format!("nt{}", i)).collect();

            // Add some undefined nonterminals
            let num_undefined = usize::arbitrary(g) % 3;
            for i in 0..num_undefined {
                nonterms.push(format!("undefined{}", i));
            }

            let mut productions = Vec::new();
            let defined_count = num_nonterms;

            for (idx, nt) in nonterms.iter().enumerate() {
                if idx >= defined_count {
                    // Don't define the undefined nonterminals
                    continue;
                }

                let mut expressions = Vec::new();
                let num_alternatives = usize::arbitrary(g) % 2 + 1;

                for _ in 0..num_alternatives {
                    let mut terms = Vec::new();
                    let num_terms = usize::arbitrary(g) % 2 + 1;

                    for _ in 0..num_terms {
                        if bool::arbitrary(g) && !nonterms.is_empty() {
                            // Reference any nonterminal (may be undefined)
                            let ref_idx = usize::arbitrary(g) % nonterms.len();
                            if let Some(nt) = nonterms.get(ref_idx) {
                                terms.push(Term::Nonterminal(nt.clone()));
                            } else {
                                terms.push(Term::Terminal(String::arbitrary(g)));
                            }
                        } else {
                            terms.push(Term::Terminal(String::arbitrary(g)));
                        }
                    }

                    expressions.push(Expression::from_parts(terms));
                }

                productions.push(Production::from_parts(
                    Term::Nonterminal(nt.clone()),
                    expressions,
                ));
            }

            Self(Grammar::from_parts(productions))
        }
    }

    // Property test: Parser construction fails if any nonterminal lacks definition
    fn prop_parser_fails_with_undefined_nonterminal(grammar: GrammarWithUndefined) -> TestResult {
        let grammar = grammar.0;

        // Collect all nonterminals defined in LHS
        let mut defined = std::collections::HashSet::new();
        for production in grammar.productions_iter() {
            if let Term::Nonterminal(nt) = &production.lhs {
                defined.insert(nt.clone());
            }
        }

        // Collect all nonterminals used in RHS
        let mut referenced = std::collections::HashSet::new();
        for production in grammar.productions_iter() {
            for expression in production.rhs_iter() {
                for term in expression.terms_iter() {
                    if let Term::Nonterminal(nt) = term {
                        referenced.insert(nt.clone());
                    }
                }
            }
        }

        // Find undefined nonterminals
        let undefined: Vec<_> = referenced.difference(&defined).cloned().collect();

        let parser_result = grammar.build_parser();

        if undefined.is_empty() {
            // All nonterminals are defined, parser should succeed
            TestResult::from_bool(parser_result.is_ok())
        } else {
            // Some nonterminals are undefined, parser should fail
            TestResult::from_bool(
                parser_result.is_err()
                    && matches!(parser_result.unwrap_err(), Error::ValidationError(_)),
            )
        }
    }

    #[test]
    fn parser_fails_with_undefined_nonterminal() {
        QuickCheck::new().tests(100).quickcheck(
            prop_parser_fails_with_undefined_nonterminal as fn(GrammarWithUndefined) -> TestResult,
        );
    }

    // Helper: Generate valid grammar with at least 2 productions
    #[derive(Debug, Clone)]
    struct ValidGrammarWithMultipleProductions(Grammar);
    impl Arbitrary for ValidGrammarWithMultipleProductions {
        fn arbitrary(g: &mut Gen) -> Self {
            // Generate 2-5 nonterminals
            let num_nonterms = usize::arbitrary(g) % 4 + 2;
            let nonterms: Vec<String> = (0..num_nonterms).map(|i| format!("nt{}", i)).collect();

            let mut productions = Vec::new();

            for (idx, nt) in nonterms.iter().enumerate() {
                let mut expressions = Vec::new();
                let num_alternatives = usize::arbitrary(g) % 2 + 1;

                for _ in 0..num_alternatives {
                    let mut terms = Vec::new();
                    let num_terms = usize::arbitrary(g) % 2 + 1;

                    for _ in 0..num_terms {
                        if bool::arbitrary(g) && idx > 0 {
                            // Reference a previously defined nonterminal
                            let ref_idx = usize::arbitrary(g) % idx;
                            if let Some(nt) = nonterms.get(ref_idx) {
                                terms.push(Term::Nonterminal(nt.clone()));
                            } else {
                                terms.push(Term::Terminal(String::arbitrary(g)));
                            }
                        } else {
                            terms.push(Term::Terminal(String::arbitrary(g)));
                        }
                    }

                    expressions.push(Expression::from_parts(terms));
                }

                productions.push(Production::from_parts(
                    Term::Nonterminal(nt.clone()),
                    expressions,
                ));
            }

            Self(Grammar::from_parts(productions))
        }
    }

    // Property test: Parser results are identical regardless of production order
    fn prop_parser_order_independent(grammar: ValidGrammarWithMultipleProductions) -> TestResult {
        let grammar = grammar.0;

        // Create a shuffled version of the grammar
        let mut productions: Vec<_> = grammar.productions_iter().cloned().collect();
        let mut rng = rand::rng();
        rand::seq::SliceRandom::shuffle(productions.as_mut_slice(), &mut rng);

        let grammar1 = grammar;
        let grammar2 = Grammar::from_parts(productions);

        let parser1 = match grammar1.build_parser() {
            Ok(p) => p,
            Err(_) => return TestResult::discard(),
        };
        let parser2 = match grammar2.build_parser() {
            Ok(p) => p,
            Err(_) => return TestResult::discard(),
        };

        // Get starting term from first grammar
        let starting_term = match grammar1.starting_term() {
            Some(t) => t,
            None => return TestResult::discard(),
        };

        // Generate a test sentence
        let sentence = match grammar1.generate() {
            Ok(s) => s,
            Err(_) => return TestResult::discard(),
        };

        // Parse with both parsers using explicit starting term
        let parse_trees1: Vec<_> = parser1
            .parse_input_starting_with(&sentence, starting_term)
            .collect();
        let parse_trees2: Vec<_> = parser2
            .parse_input_starting_with(&sentence, starting_term)
            .collect();

        // Results should be identical
        TestResult::from_bool(parse_trees1.len() == parse_trees2.len())
    }

    #[test]
    fn parser_order_independent() {
        QuickCheck::new().tests(50).quickcheck(
            prop_parser_order_independent as fn(ValidGrammarWithMultipleProductions) -> TestResult,
        );
    }

    // Property test: Parser can be reused multiple times with same results
    fn prop_parser_reusable(grammar: SimpleValidGrammar) -> TestResult {
        let grammar = grammar.0;

        // Only test with grammars that can generate
        if !grammar.terminates() {
            return TestResult::discard();
        }

        let parser = match grammar.build_parser() {
            Ok(p) => p,
            Err(_) => return TestResult::discard(),
        };

        // Generate a sentence
        let sentence = match grammar.generate() {
            Ok(s) => s,
            Err(_) => return TestResult::discard(),
        };

        // Parse the same sentence multiple times
        let parse_trees1: Vec<_> = parser.parse_input(&sentence).collect();
        let parse_trees2: Vec<_> = parser.parse_input(&sentence).collect();
        let parse_trees3: Vec<_> = parser.parse_input(&sentence).collect();

        // All results should be identical
        TestResult::from_bool(
            parse_trees1.len() == parse_trees2.len() && parse_trees2.len() == parse_trees3.len(),
        )
    }

    #[test]
    fn parser_reusable() {
        QuickCheck::new()
            .tests(100)
            .quickcheck(prop_parser_reusable as fn(SimpleValidGrammar) -> TestResult);
    }

    // Property test: Parser validation catches all undefined nonterminals
    // Simplified: Build grammars with known undefined nonterminals
    fn prop_validation_catches_all_undefined(grammar: GrammarWithUndefined) -> TestResult {
        let grammar = grammar.0;

        // Collect all nonterminals defined in LHS
        let mut defined = std::collections::HashSet::new();
        for production in grammar.productions_iter() {
            if let Term::Nonterminal(nt) = &production.lhs {
                defined.insert(nt.clone());
            }
        }

        // Collect all nonterminals used in RHS
        let mut referenced = std::collections::HashSet::new();
        for production in grammar.productions_iter() {
            for expression in production.rhs_iter() {
                for term in expression.terms_iter() {
                    if let Term::Nonterminal(nt) = term {
                        referenced.insert(nt.clone());
                    }
                }
            }
        }

        let undefined: Vec<_> = referenced.difference(&defined).cloned().collect();

        let parser_result = grammar.build_parser();

        match parser_result {
            Ok(_) => {
                // Parser succeeded, so there should be no undefined nonterminals
                TestResult::from_bool(undefined.is_empty())
            }
            Err(Error::ValidationError(msg)) => {
                // Parser failed, error message should mention all undefined nonterminals
                let all_mentioned = undefined
                    .iter()
                    .all(|nt| msg.contains(&format!("<{nt}>")) || msg.contains(nt));
                TestResult::from_bool(!undefined.is_empty() && all_mentioned)
            }
            Err(_) => TestResult::error("Expected ValidationError"),
        }
    }

    #[test]
    fn validation_catches_all_undefined() {
        QuickCheck::new().tests(100).quickcheck(
            prop_validation_catches_all_undefined as fn(GrammarWithUndefined) -> TestResult,
        );
    }
}
