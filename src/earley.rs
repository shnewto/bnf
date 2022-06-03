use crate::{Grammar, Production, Term};

#[derive(Debug, PartialEq)]
struct EarleyState<'a> {
    lhs: &'a Term,
    unmatched: crate::expression::Iter<'a>,
    input: &'a str,
}

impl<'a> EarleyState<'a> {
    pub fn new(lhs: &'a Term, unmatched: crate::expression::Iter<'a>, input: &'a str) -> Self {
        Self {
            lhs,
            unmatched,
            input,
        }
    }
    pub fn from_production(
        production: &'a Production,
        input: &'a str,
    ) -> impl Iterator<Item = EarleyState<'a>> {
        let lhs = &production.lhs;
        production.rhs_iter().map(move |expression| {
            let unmatched = expression.terms_iter();
            Self {
                lhs,
                unmatched,
                input,
            }
        })
    }
    pub fn predict(
        &self,
        grammar: &'a Grammar,
        input: &'a str,
    ) -> impl Iterator<Item = EarleyState<'a>> {
        // TODO: next unmatched must be nonterm!
        let next_unmatched = self.unmatched.clone().next().unwrap();

        grammar
            .productions_iter()
            .filter(|prod| prod.lhs == *next_unmatched)
            .flat_map(|prod| EarleyState::from_production(prod, input))
    }
}

#[derive(Debug, PartialEq, Eq)]
struct EarleyParser {}

impl EarleyParser {
    pub fn new() -> Self {
        EarleyParser {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Expression, Grammar};

    fn parse_dna_grammar() -> Grammar {
        "<dna> ::= <base> <dna> | <base>
    <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap()
    }

    struct ExplicitDnaTestGrammar {
        grammar: Grammar,
        prod_dna: Production,
        prod_base: Production,
        expr_base: Expression,
        expr_base_and_dna: Expression,
        expr_a: Expression,
        expr_c: Expression,
        expr_g: Expression,
        expr_t: Expression,
        nonterm_dna: Term,
        nonterm_base: Term,
        term_a: Term,
        term_c: Term,
        term_g: Term,
        term_t: Term,
    }

    // this is fiddly, but giving named access to each part of the DNA grammar
    // helps with test clarity below
    fn build_explicit_dna_grammar() -> ExplicitDnaTestGrammar {
        let grammar = parse_dna_grammar();
        let prods: Vec<_> = grammar.productions_iter().collect();
        let prod_dna = prods[0].clone();
        let prod_dna_exprs: Vec<_> = prod_dna.rhs_iter().collect();
        let expr_base = prod_dna_exprs[0].clone();
        let expr_base_and_dna = prod_dna_exprs[1].clone();

        let prod_base = prods[1].clone();
        let prod_base_exprs: Vec<_> = prod_base.rhs_iter().collect();

        let expr_a = prod_base_exprs[0].clone();
        let expr_c = prod_base_exprs[1].clone();
        let expr_g = prod_base_exprs[2].clone();
        let expr_t = prod_base_exprs[3].clone();

        let nonterm_dna = prod_dna.lhs.clone();
        let nonterm_base = prod_base.lhs.clone();

        let term_a = prod_base_exprs[0].terms_iter().next().unwrap().clone();
        let term_c = prod_base_exprs[1].terms_iter().next().unwrap().clone();
        let term_g = prod_base_exprs[2].terms_iter().next().unwrap().clone();
        let term_t = prod_base_exprs[3].terms_iter().next().unwrap().clone();

        ExplicitDnaTestGrammar {
            grammar,
            prod_dna,
            expr_base,
            expr_base_and_dna,
            prod_base,
            expr_a,
            expr_c,
            expr_g,
            expr_t,
            nonterm_dna,
            nonterm_base,
            term_a,
            term_c,
            term_g,
            term_t,
        }
    }

    fn earley_state_from_grammar<'a>(grammar: &'a Grammar, input: &'a str) -> EarleyState<'a> {
        let production = grammar.productions_iter().next().unwrap();
        EarleyState::from_production(production, input)
            .next()
            .unwrap()
    }

    #[test]
    fn earley_parse_dna() {
        let grammar = parse_dna_grammar();
        let input = "G A T A C A".split_whitespace();

        let mut parses = grammar.parse(input);
        assert!(matches!(parses.next(), Some(_)));
    }

    #[test]
    fn earley_parse_alien_dna() {
        let grammar = parse_dna_grammar();
        let input = "L O L O L O L".split_whitespace();

        let mut parses = grammar.parse(input);
        assert!(matches!(parses.next(), None));
    }

    #[test]
    fn predict_none() {
        let grammar = parse_dna_grammar();
        let input = "T";
        let curr = earley_state_from_grammar(&grammar, input);
        let predicted: Vec<_> = curr.predict(&grammar, input).collect();

        assert_eq!(predicted, vec![]);
    }

    #[test]
    fn predict_some() {
        let dna = build_explicit_dna_grammar();
        let input = "T";
        let curr = earley_state_from_grammar(&dna.grammar, input);
        println!("{:#?}", curr);

        let predictions: Vec<_> = curr.predict(&dna.grammar, input).collect();

        // should have predicted from "<dna>" to "<base>" | "<base> <dna>"
        let expected = vec![
            EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter(), input),
            EarleyState::new(&dna.nonterm_base, dna.expr_c.terms_iter(), input),
            EarleyState::new(&dna.nonterm_base, dna.expr_g.terms_iter(), input),
            EarleyState::new(&dna.nonterm_base, dna.expr_t.terms_iter(), input),
            EarleyState::new(&dna.nonterm_dna, dna.expr_base_and_dna.terms_iter(), input),
        ];
        assert_eq!(predictions, expected);
    }

    #[test]
    fn scan() {
        todo!()
    }

    #[test]
    fn complete() {
        todo!()
    }
}
