#![cfg(test)]

use bnf::{Grammar, Term};

#[test]
fn iterate_grammar() {
    let dna_productions = "
        <dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'";

    let dna_grammar: Grammar = dna_productions.parse().unwrap();

    let left_hand_terms: Vec<&Term> = dna_grammar
        .productions_iter()
        .map(|prod| &prod.lhs)
        .collect();

    // should be as many left hand terms as productions
    assert_eq!(
        dna_grammar.productions_iter().count(),
        left_hand_terms.len()
    );

    let right_hand_terms: Vec<&Term> = dna_grammar
        .productions_iter()
        .flat_map(|prod| prod.rhs_iter())
        .flat_map(|expr| expr.terms_iter())
        .collect();

    // check nonterminals are in left and right hand terms collection
    for term in ["dna", "base"].iter() {
        let expected_nonterminal = Term::nonterminal(*term);

        assert!(
            left_hand_terms.contains(&&expected_nonterminal),
            "{expected_nonterminal} was not in left hand terms"
        );

        assert!(
            right_hand_terms.contains(&&expected_nonterminal),
            "{expected_nonterminal} was not in right hand terms"
        );
    }

    // any term which appears on the right but not left is a terminal
    let mut only_right_terms = right_hand_terms
        .into_iter()
        .filter(|term| !left_hand_terms.contains(term));

    // check terminals are only on right hand side
    for term in ["A", "C", "G", "T"].iter() {
        let expected_terminal = Term::terminal(*term);

        assert!(
            only_right_terms.any(|e| e == &expected_terminal),
            "{expected_terminal} was not in left hand terms"
        );
    }
}

#[test]
fn mutably_iterate_grammar() {
    let dna_productions = "
        <dna> ::= <dna> | <base> <dna>;
        <base> ::= 'A' | 'C' | 'G' | 'T';";

    let mut dna_grammar: Grammar = dna_productions.parse().unwrap();

    // scope mutable borrow
    {
        let terminals = dna_grammar
            .productions_iter_mut()
            .flat_map(|prod| prod.rhs_iter_mut())
            .flat_map(|expr| expr.terms_iter_mut())
            .filter(|&&mut ref term| matches!(*term, Term::Terminal(_)));

        // transform all terminals to "Z"
        for term in terminals {
            *term = Term::terminal("Z");
        }
    }

    // get another iterator to check work
    let are_all_terminals_z = dna_grammar
        .productions_iter()
        .flat_map(|prod| prod.rhs_iter())
        .flat_map(|expr| expr.terms_iter())
        .filter(|&term| matches!(*term, Term::Terminal(_)))
        .all(|term| match term {
            Term::Terminal(s) => s.as_ref() == "Z",
            _ => false,
        });

    assert!(
        are_all_terminals_z,
        "all terminals in {dna_grammar} were not \"Z\""
    );
}
