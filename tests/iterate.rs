extern crate bnf;
use bnf::node::Term;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iterate_grammar() {
        let dna_productions = "
            <dna> ::= <base> | <base> <dna>
            <base> ::= \"A\" | \"C\" | \"G\" | \"T\"";

        let dna_grammar = bnf::parse(dna_productions);

        let left_hand_terms: Vec<&Term> = dna_grammar
            .productions_iter()
            .map(|ref prod| &prod.lhs)
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
        for term in ["dna", "base"].into_iter() {
            let term_string = String::from(*term);
            let expected_nonterminal = Term::Nonterminal(term_string);

            assert!(
                left_hand_terms.contains(&&expected_nonterminal),
                "{} was not in left hand terms",
                expected_nonterminal
            );

            assert!(
                right_hand_terms.contains(&&expected_nonterminal),
                "{} was not in right hand terms",
                expected_nonterminal
            );
        }

        // any term which appears on the right but not left is a terminal
        let only_right_terms: Vec<&Term> = right_hand_terms
            .into_iter()
            .filter(|term| !left_hand_terms.contains(term))
            .collect();

        // check terminals are only on right hand side
        for term in ["A", "C", "G", "T"].into_iter() {
            let term_string = String::from(*term);
            let expected_terminal = Term::Terminal(term_string);

            assert!(
                only_right_terms.contains(&&expected_terminal),
                "{} was not in left hand terms",
                expected_terminal
            );
        }
    }

    #[test]
    fn mutably_iterate_grammar() {
        let dna_productions = "
            <dna> ::= <dna> | <base> <dna>;
            <base> ::= \"A\" | \"C\" | \"G\" | \"T\";";

        let mut dna_grammar = bnf::parse(dna_productions);

        // scope mutable borrow
        {
            let terminals = dna_grammar
                .productions_iter_mut()
                .flat_map(|prod| prod.rhs_iter_mut())
                .flat_map(|expr| expr.terms_iter_mut())
                .filter(|&&mut ref term| match *term {
                    Term::Terminal(_) => true,
                    _ => false,
                });

            // transform all terminals to "Z"
            for term in terminals {
                *term = Term::Terminal(String::from("Z"));
            }
        }

        // get another iterator to check work
        let are_all_terminals_z = dna_grammar
            .productions_iter()
            .flat_map(|prod| prod.rhs_iter())
            .flat_map(|expr| expr.terms_iter())
            .filter(|&term| match *term {
                Term::Terminal(_) => true,
                _ => false,
            })
            .all(|term| match *term {
                Term::Terminal(ref s) => *s == String::from("Z"),
                _ => false,
            });

        assert!(
            are_all_terminals_z,
            "all terminals in {} were not \"Z\"",
            dna_grammar
        );
    }
}
