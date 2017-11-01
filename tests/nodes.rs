extern crate bnf;
use bnf::node::{Expression, Grammar, Production, Term};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_expressions() {
        let t1: Term = Term::Terminal(String::from("terminal"));
        let nt1: Term = Term::Nonterminal(String::from("nonterminal"));
        let t2: Term = Term::Terminal(String::from("terminal"));
        let nt2: Term = Term::Nonterminal(String::from("nonterminal"));

        let e1: Expression = Expression::from_parts(vec![nt1, t1]);
        let mut e2: Expression = Expression::new();
        e2.add_term(nt2);
        e2.add_term(t2);

        assert_eq!(e1, e2);
    }

    #[test]
    fn new_productions() {
        let lhs1: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs1: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p1: Production = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs2: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let mut p2: Production = Production::new();
        p2.lhs = lhs2;
        p2.add_to_rhs(rhs2);

        assert_eq!(p1, p2);
    }

    #[test]
    fn new_grammars() {
        let lhs1: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs1: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p1: Production = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs2: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p2: Production = Production::from_parts(lhs2, vec![rhs2]);

        let mut g1: Grammar = Grammar::new();
        g1.add_production(p1.clone());
        g1.add_production(p2.clone());
        let g2: Grammar = Grammar::from_parts(vec![p1, p2]);
        assert_eq!(g1, g2);
    }

    #[test]
    fn iterate_grammar() {
        let dna_productions = "
            <dna> ::= <dna> | <base> <dna>;
            <base> ::= \"A\" | \"C\" | \"G\" | \"T\";";

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
}
