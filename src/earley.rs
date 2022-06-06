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
    pub fn scan(&self, curr: &'a str, next: &'a str) -> Option<Self> {
        let mut unmatched = self.unmatched.clone();

        let next_unmatched = unmatched.next();

        next_unmatched
            .and_then(|next_term| match next_term {
                Term::Nonterminal(_) => None,
                Term::Terminal(term) => (term == curr).then(|| ()),
            })
            .is_some()
            .then(|| EarleyState {
                lhs: self.lhs,
                unmatched,
                input: next,
            })
    }
    pub fn complete(&self, parent: &'a EarleyState) -> Option<Self> {
        let mut unmatched = parent.unmatched.clone();
        let next_unmatched = unmatched.next();

        next_unmatched
            .and_then(|parent_unmatched| (parent_unmatched == self.lhs).then(|| ()))
            .is_some()
            .then(|| EarleyState {
                lhs: parent.lhs,
                unmatched,
                input: self.input,
            })
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
        // some testing utilities default to the first expression in a production
        // so this has "<base> <dna>" *before* "<base>"
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
        let expr_base_and_dna = prod_dna_exprs[0].clone();
        let expr_base = prod_dna_exprs[1].clone();

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

    // WARNING: only returns first EarleyState, for testing ergonomics
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
        let unknown_production: Production = "<unknown> ::= <number>".parse().unwrap();
        let curr = EarleyState::from_production(&unknown_production, input)
            .next()
            .unwrap();

        // predict from non terminal which has no production in the grammar
        let mut next = curr.predict(&grammar, input);

        // no matching production, so no predictions
        assert_eq!(next.next(), None);
    }

    #[test]
    fn predict_some() {
        // predict on "<dna> ::= $ <base> <dna>"
        let dna = build_explicit_dna_grammar();
        let input = "T";
        let curr = earley_state_from_grammar(&dna.grammar, input);

        let next: Vec<_> = curr.predict(&dna.grammar, input).collect();

        // expect predictions of:
        // * <base> ::= $ "A"
        // * <base> ::= $ "C"
        // * <base> ::= $ "G"
        // * <base> ::= $ "T"
        let expected = vec![
            EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter(), input),
            EarleyState::new(&dna.nonterm_base, dna.expr_c.terms_iter(), input),
            EarleyState::new(&dna.nonterm_base, dna.expr_g.terms_iter(), input),
            EarleyState::new(&dna.nonterm_base, dna.expr_t.terms_iter(), input),
        ];
        assert_eq!(next, expected);
    }

    #[test]
    fn scan_none() {
        // scan on '<base> ::= $ "A"'
        let dna = build_explicit_dna_grammar();
        let input = "T";
        let next_input = "A";
        let curr = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter(), input);

        // attempt to scan "A", but with input "T"
        let next = curr.scan(input, next_input);

        // input does not match scan
        assert_eq!(next, None);
    }

    #[test]
    fn scan_some() {
        // scan on '<base> ::= $ "A"'
        let dna = build_explicit_dna_grammar();
        let input = "A";
        let next_input = "T";
        let curr = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter(), input);

        // attempt to scan "A", with input "A"
        let next = curr.scan(input, next_input).unwrap();

        // expect new state '<base> ::= "A" $' (note $ is after terminal "A" b/c it has been scanned)
        assert_eq!(next.lhs, &dna.nonterm_base);
        assert_eq!(next.input, next_input);
        assert_eq!(next.unmatched.clone().next(), None);
    }

    #[test]
    fn complete_none() {
        // complete on '<base> ::= "A" $' BUT mismatched parent state '<dna> ::= $ <dna> <base>'
        let dna = build_explicit_dna_grammar();
        let input = "A";
        let next_input = "T";
        let prev = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter(), input);
        let scanned_base = prev.scan("A", next_input).unwrap();
        let parent_mistached_production: Production = "<dna> ::= <dna> <base>".parse().unwrap();
        let parent_state = EarleyState::from_production(&parent_mistached_production, input)
            .next()
            .unwrap();

        // complete because at end of production
        let next = scanned_base.complete(&parent_state);

        // results in no new state
        assert_eq!(next, None);
    }

    #[test]
    fn complete_some() {
        // complete on '<base> ::= "A" $' AND '<dna> ::= $ <base> <dna>'
        let dna = build_explicit_dna_grammar();
        let input = "A";
        let next_input = "T";
        let prev = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter(), input);
        let scanned_base = prev.scan("A", next_input).unwrap();
        let parent_state =
            EarleyState::new(&dna.nonterm_dna, dna.expr_base_and_dna.terms_iter(), input);

        // complete because at end of production
        let next = scanned_base.complete(&parent_state).unwrap();

        // results in new state: '<dna> ::= <base> $ <dna>'
        let mut unmatched = parent_state.unmatched.clone();
        unmatched.next();
        let expected = EarleyState::new(&dna.nonterm_dna, unmatched, next_input);
        assert_eq!(next, expected);
    }
}

// NEXT
// * probably need to require "Peek" on Expression Iters, because predict/scan/complete depend on next
// * grammar::parse
// * test both left and right recursive grammars
// * restructure module layout? naming it "earley" seems wrong...
// * docs

// STRETCH
// * can tests be written in more natural string descriptions like "<dna> ::= $ <base> <dna>", maybe extend existing parsers?
