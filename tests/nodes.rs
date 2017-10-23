extern crate bnf;
use bnf::node::{Term, Expression, Production, Grammar};

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
        e2.terms.push(nt2);
        e2.terms.push(t2);

        assert_eq!(e1, e2);
    }

    #[test]
    fn new_productions() {
        let lhs1: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs1: Expression = Expression::from_parts(
            vec![
                Term::Terminal(String::from("STRING B")),
                Term::Nonterminal(String::from("STRING C"))]);
        let p1: Production = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs2: Expression = Expression::from_parts(
            vec![
                Term::Terminal(String::from("STRING B")),
                Term::Nonterminal(String::from("STRING C"))]);
        let mut p2: Production = Production::new();
        p2.lhs = lhs2;
        p2.rhs = vec![rhs2];

        assert_eq!(p1, p2);
    }

    #[test]
    fn new_grammars() {
        let lhs1: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs1: Expression = Expression::from_parts(
            vec![
                Term::Terminal(String::from("STRING B")),
                Term::Nonterminal(String::from("STRING C"))]);
        let p1: Production = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs2: Expression = Expression::from_parts(
            vec![
                Term::Terminal(String::from("STRING B")),
                Term::Nonterminal(String::from("STRING C"))]);
        let p2: Production = Production::from_parts(lhs2, vec![rhs2]);

        let mut g1: Grammar = Grammar::new();
        g1.productions.push(p1.clone());
        g1.productions.push(p2.clone());
        let g2: Grammar = Grammar::from_parts(vec![p1, p2]);
        assert_eq!(g1, g2);
    }
}