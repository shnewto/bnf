use crate::{grammar, Grammar, Production, Term};
use std::pin::Pin;

#[derive(Debug, PartialEq)]
struct EarleyState<'gram> {
    lhs: &'gram Term,
    matching: Option<&'gram Term>,
    unmatched: crate::expression::Iter<'gram>,
}

impl<'gram> EarleyState<'gram> {
    pub fn new(lhs: &'gram Term, mut unmatched: crate::expression::Iter<'gram>) -> Self {
        let matching = unmatched.next();
        Self {
            lhs,
            matching,
            unmatched,
        }
    }
    pub fn from_production(production: &'gram Production) -> impl Iterator<Item = EarleyState<'_>> {
        production.rhs_iter().map(move |expression| {
            let unmatched = expression.terms_iter();
            Self::new(&production.lhs, unmatched)
        })
    }
    pub fn predict(
        &'gram self,
        grammar: &'gram Grammar,
    ) -> impl Iterator<Item = EarleyState<'gram>> {
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
    pub fn complete(&self, parent: &'gram EarleyState<'_>) -> Option<Self> {
        parent
            .matching
            .and_then(|matching| (matching == self.lhs).then(|| ()))
            .is_some()
            .then(|| EarleyState::new(parent.lhs, parent.unmatched.clone()))
    }
}

struct EarleyStateSet<'gram> {
    arena: typed_arena::Arena<EarleyState<'gram>>,
    unprocessed: Vec<std::ptr::NonNull<EarleyState<'gram>>>,
    _pinned: std::marker::PhantomPinned,
}

impl<'gram> EarleyStateSet<'gram> {
    pub fn new() -> Self {
        Self {
            arena: typed_arena::Arena::new(),
            unprocessed: Vec::new(),
            _pinned: std::marker::PhantomPinned,
        }
    }
    pub fn alloc_extend(self: Pin<&mut Self>, iter: impl Iterator<Item = EarleyState<'gram>>) {
        let this = unsafe { self.get_unchecked_mut() };
        let allocated = this.arena.alloc_extend(iter);

        let allocated_ptrs = allocated
            .iter_mut()
            .map(|i| unsafe { std::ptr::NonNull::new_unchecked(i) });

        this.unprocessed.extend(allocated_ptrs);
    }
    pub fn pop_unprocessed(self: Pin<&mut Self>) -> Option<&mut EarleyState<'gram>> {
        let this = unsafe { self.get_unchecked_mut() };
        this.unprocessed.pop().map(|mut i| unsafe { i.as_mut() })
    }
}

pub fn parse<'gram, 'input>(
    grammar: &'gram Grammar,
    mut input_iter: impl Iterator<Item = &'input str>,
) -> impl Iterator<Item = grammar::ParseTree> {
    // init queue with all productions in start/first rule
    let start_production = match grammar.productions_iter().next() {
        None => return std::iter::empty(),
        Some(prod) => prod,
    };

    let start_states = EarleyState::from_production(start_production);

    let mut state_set = EarleyStateSet::new();
    let mut state_set = unsafe { std::pin::Pin::new_unchecked(&mut state_set) };

    while let Some(state) = state_set.as_mut().pop_unprocessed() {
        match state.matching {
            // predict
            Some(Term::Nonterminal(_)) => {
                let predictions = state.predict(grammar);
                // TODO: de-dupe!
                // state_set.as_mut().alloc_extend(predictions);
            }
            // scan
            Some(Term::Terminal(_)) => {
                // if let Some(scanned) = state.scan(input) {
                // state_set.push_unprocessed(scanned);
                // input = input_iter.next();
                // }
            }
            // complete
            None => {
                // TODO: can be multiple completions
                // let completions = state.complete(parent);
                // state_set.extend_unprocessed(completions);
                // TODO: when completing, if "starting" state, then add to successes
            }
        };
    }

    std::iter::empty()
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

        let input = "G A T A C A".split_whitespace();

        let mut parses = parse(&grammar, input);
        assert!(matches!(parses.next(), Some(_)));
    }

    #[test]
    fn parse_dna_left_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <dna> <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "G A T A C A".split_whitespace();

        let mut parses = parse(&grammar, input);
        assert!(matches!(parses.next(), Some(_)));
    }

    #[test]
    fn parse_dna_alien() {
        let grammar: Grammar = "<dna> ::= <base> <dna> | <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "L O L O L O L".split_whitespace();

        let mut parses = parse(&grammar, input);
        assert!(matches!(parses.next(), None));
    }
}

// NEXT
// * does "complete" need to advance *all* parents with matching non-term ? seems like it....
// * test ambiguous grammar parse: "<start> ::= <a> | <b>, <a> ::= FIN, <b> ::= FIN", should have BOTH parse trees
// * test example from earley website
// * EarleyParser PARSES
// * EarleyState::advance_cursor probably nice ergonomics
// * what should "failure" modes of parsing look like? Result<Iter> ? fail to predict/scan/complete? can errors include context?
// * grammar::parse
// * pretty printing of parse trees?
// * perf testing
// * clippy
// * property tests?
// * restructure module layout? naming it "earley" seems wrong...
// * docs

// STRETCH
// * can tests be written in more natural string descriptions like "<dna> ::= $ <base> <dna>", maybe extend existing parsers?
