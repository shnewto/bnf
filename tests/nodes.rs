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

    #[test]
    fn add_term_to_expression() {
        let mut terms = vec![
            Term::Terminal(String::from("A")),
            Term::Terminal(String::from("C")),
            Term::Terminal(String::from("G")),
        ];

        let mut dna_expression = Expression::from_parts(terms.clone());
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // oops forgot "T"
        let forgotten = Term::Terminal(String::from("T"));
        dna_expression.add_term(forgotten.clone());
        terms.push(forgotten);
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // check all terms are there
        for term in dna_expression.terms_iter() {
            assert!(terms.contains(term), "{} was not in terms", term);
        }
    }

    #[test]
    fn remove_term_from_expression() {
        let terms = vec![
            Term::Terminal(String::from("A")),
            Term::Terminal(String::from("C")),
            Term::Terminal(String::from("G")),
            Term::Terminal(String::from("T")),
            Term::Terminal(String::from("Z")),
        ];

        let mut dna_expression = Expression::from_parts(terms.clone());
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // oops "Z" isn't a dna base
        let accident = Term::Terminal(String::from("Z"));
        let removed = dna_expression.remove_term(&accident);

        // the removed element should be the accident
        assert_eq!(Some(accident.clone()), removed);
        // number of terms should have decreased
        assert_eq!(dna_expression.terms_iter().count(), terms.len() - 1);
        // the accident should no longer be found in the terms
        assert_eq!(
            dna_expression.terms_iter().find(|&term| *term == accident),
            None
        );
    }

    #[test]
    fn remove_nonexistent_term_from_expression() {
        let terms = vec![
            Term::Terminal(String::from("A")),
            Term::Terminal(String::from("C")),
            Term::Terminal(String::from("G")),
            Term::Terminal(String::from("T")),
        ];

        let mut dna_expression = Expression::from_parts(terms.clone());
        assert_eq!(dna_expression.terms_iter().count(), terms.len());

        // oops "Z" isn't a dna base
        let nonexistent = Term::Terminal(String::from("Z"));
        let removed = dna_expression.remove_term(&nonexistent);

        // the removed element should be the accident
        assert_eq!(None, removed);
        // number of terms should not have decreased
        assert_eq!(dna_expression.terms_iter().count(), terms.len());
    }
}
