use crate::{grammar, Grammar, Production, Term};

#[derive(Debug, PartialEq)]
struct EarleyState<'a> {
    lhs: &'a Term,
    matching: Option<&'a Term>,
    unmatched: crate::expression::Iter<'a>,
}

impl<'a> EarleyState<'a> {
    pub fn new(lhs: &'a Term, mut unmatched: crate::expression::Iter<'a>) -> Self {
        let matching = unmatched.next();
        Self {
            lhs,
            matching,
            unmatched,
        }
    }
    pub fn from_production(production: &'a Production) -> impl Iterator<Item = EarleyState<'a>> {
        let lhs = &production.lhs;
        production.rhs_iter().map(move |expression| {
            let unmatched = expression.terms_iter();
            Self::new(lhs, unmatched)
        })
    }
    pub fn predict(&'a self, grammar: &'a Grammar) -> impl Iterator<Item = EarleyState<'a>> {
        grammar
            .productions_iter()
            .filter(|prod| prod.lhs == *self.matching.unwrap())
            .flat_map(|prod| EarleyState::from_production(prod))
    }
    pub fn scan(&self, input: &str) -> Option<Self> {
        self.matching
            .and_then(|next_term| match next_term {
                Term::Nonterminal(_) => unreachable!(),
                Term::Terminal(term) => (term == input).then(|| ()),
            })
            .is_some()
            .then(|| EarleyState::new(self.lhs, self.unmatched.clone()))
    }
    pub fn complete(&self, parent: &EarleyState<'a>) -> Option<Self> {
        parent
            .matching
            .and_then(|matching| (matching == self.lhs).then(|| ()))
            .is_some()
            .then(|| EarleyState::new(parent.lhs, parent.unmatched.clone()))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct EarleyParser<'a> {
    grammar: &'a Grammar,
}

impl<'a> EarleyParser<'a> {
    pub fn new(grammar: &'a Grammar) -> Self {
        EarleyParser { grammar }
    }

    pub fn parse<'input>(
        &self,
        mut input_iter: impl Iterator<Item = &'input str>,
    ) -> impl Iterator<Item = grammar::ParseTree> {
        // init queue with all productions in start/first rule
        let start_production = match self.grammar.productions_iter().next() {
            None => return std::iter::empty(),
            Some(prod) => prod,
        };

        let arena = typed_arena::Arena::<EarleyState>::new();
        let starters = arena.alloc_extend(EarleyState::from_production(start_production));

        let mut items: Vec<&mut EarleyState> = starters.iter_mut().collect();
        let mut input = input_iter.next();

        while let Some(item) = items.pop() {
            match item.matching {
                // predict
                Some(Term::Nonterminal(_)) => {
                    let predictions = item.predict(self.grammar);
                    // add to arena, with parent set?
                    // add arena references to queue
                }
                // scan
                Some(Term::Terminal(_)) => {
                    // add to arena, with parent set?
                    // add arena references to queue
                    // advance to next token
                    input = input_iter.next();
                }
                // complete
                None => {
                    // add new completions to arena, with parent set?
                    // add arena references to queue
                    // when completing, if "starting" state, then add to successes
                }
            };
        }

        std::iter::empty()
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
    fn earley_state_from_grammar<'a>(grammar: &'a Grammar) -> EarleyState<'a> {
        let production = grammar.productions_iter().next().unwrap();
        EarleyState::from_production(production).next().unwrap()
    }

    #[test]
    fn predict_none() {
        let grammar = parse_dna_grammar();
        let unknown_production: Production = "<unknown> ::= <number>".parse().unwrap();
        let curr = EarleyState::from_production(&unknown_production)
            .next()
            .unwrap();

        // predict from non terminal which has no production in the grammar
        let mut next = curr.predict(&grammar);

        // no matching production, so no predictions
        assert_eq!(next.next(), None);
    }

    #[test]
    fn predict_some() {
        // predict on "<dna> ::= $ <base> <dna>"
        let dna = build_explicit_dna_grammar();
        let curr = earley_state_from_grammar(&dna.grammar);

        let next: Vec<_> = curr.predict(&dna.grammar).collect();

        // expect predictions of:
        // * <base> ::= $ "A"
        // * <base> ::= $ "C"
        // * <base> ::= $ "G"
        // * <base> ::= $ "T"
        let expected = vec![
            EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter()),
            EarleyState::new(&dna.nonterm_base, dna.expr_c.terms_iter()),
            EarleyState::new(&dna.nonterm_base, dna.expr_g.terms_iter()),
            EarleyState::new(&dna.nonterm_base, dna.expr_t.terms_iter()),
        ];
        assert_eq!(next, expected);
    }

    #[test]
    fn scan_none() {
        // scan on '<base> ::= $ "A"'
        let dna = build_explicit_dna_grammar();
        let input = "T";
        let curr = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter());

        // attempt to scan "A", but with input "T"
        let next = curr.scan(input);

        // input does not match scan
        assert_eq!(next, None);
    }

    #[test]
    fn scan_some() {
        // scan on '<base> ::= $ "A"'
        let dna = build_explicit_dna_grammar();
        let input = "A";
        let curr = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter());

        // attempt to scan "A", with input "A"
        let next = curr.scan(input).unwrap();

        // expect new state '<base> ::= "A" $' (note $ is after terminal "A" b/c it has been scanned)
        assert_eq!(next.lhs, &dna.nonterm_base);
        assert_eq!(next.unmatched.clone().next(), None);
    }

    #[test]
    fn complete_none() {
        // complete on '<base> ::= "A" $' BUT mismatched parent state '<dna> ::= $ <dna> <base>'
        let dna = build_explicit_dna_grammar();
        let input = "A";
        let prev = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter());
        let scanned_base = prev.scan(input).unwrap();
        let parent_mistached_production: Production = "<dna> ::= <dna> <base>".parse().unwrap();
        let parent_state = EarleyState::from_production(&parent_mistached_production)
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
        let prev = EarleyState::new(&dna.nonterm_base, dna.expr_a.terms_iter());
        let scanned_base = prev.scan(input).unwrap();
        let parent_state = EarleyState::new(&dna.nonterm_dna, dna.expr_base_and_dna.terms_iter());

        // complete because at end of production
        let next = scanned_base.complete(&parent_state).unwrap();

        // results in new state: '<dna> ::= <base> $ <dna>'
        let mut unmatched = dna.expr_base_and_dna.terms_iter();
        unmatched.next();
        let expected = EarleyState::new(&dna.nonterm_dna, unmatched);
        assert_eq!(next, expected);
    }

    #[test]
    fn parse_dna_right_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();
        let parser = EarleyParser::new(&grammar);

        let input = "G A T A C A".split_whitespace();

        let mut parses = parser.parse(input);
        assert!(matches!(parses.next(), Some(_)));
    }

    #[test]
    fn parse_dna_left_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <dna> <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();
        let parser = EarleyParser::new(&grammar);

        let input = "G A T A C A".split_whitespace();

        let mut parses = parser.parse(input);
        assert!(matches!(parses.next(), Some(_)));
    }

    #[test]
    fn parse_dna_alien() {
        let grammar: Grammar = "<dna> ::= <base> <dna> | <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();
        let parser = EarleyParser::new(&grammar);

        let input = "L O L O L O L".split_whitespace();

        let mut parses = parser.parse(input);
        assert!(matches!(parses.next(), None));
    }
}

// NEXT
// * probably need to require "Peek" on Expression Iters, because predict/scan/complete depend on next
// * test ambiguous grammar parse: "<start> ::= <a> | <b>, <a> ::= FIN, <b> ::= FIN", should have BOTH parse trees
// * test example from earley website
// * does "complete" need to advance *all* parents with matching non-term ? seems like it....
// * EarleyState::advance_cursor probably nice ergonomics
// * what should "failure" modes of parsing look like? Result<Iter> ? fail to predict/scan/complete? can errors include context?
// * EarleyParser PARSES
// * grammar::parse
// * pretty printing of parse trees?
// * perf testing
// * clippy
// * property tests?
// * restructure module layout? naming it "earley" seems wrong...
// * docs

// STRETCH
// * can tests be written in more natural string descriptions like "<dna> ::= $ <base> <dna>", maybe extend existing parsers?
