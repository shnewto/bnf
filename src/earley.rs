use crate::{
    grammar::{ParseTree, ParseTreeMatch},
    Term,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ProductionId(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct StateId(usize);

struct Production<'gram> {
    id: ProductionId,
    lhs: &'gram Term,
    rhs: &'gram crate::Expression,
}

struct Grammar<'gram> {
    starting_production_ids: Vec<ProductionId>,
    productions: Vec<Production<'gram>>,
    production_ids_by_lhs: std::collections::HashMap<&'gram Term, Vec<ProductionId>>,
}

impl<'gram> Grammar<'gram> {
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
        let starting_term = &grammar
            .productions_iter()
            .next()
            .expect("Grammar must have one production to parse")
            .lhs;

        let productions: Vec<Production> = grammar
            .productions_iter()
            .flat_map(|prod| prod.rhs_iter().map(|rhs| (&prod.lhs, rhs)))
            .enumerate()
            .map(|(idx, (lhs, rhs))| Production {
                id: ProductionId(idx),
                lhs,
                rhs,
            })
            .collect();

        let mut production_ids_by_lhs = std::collections::HashMap::new();

        for prod in productions.iter() {
            production_ids_by_lhs
                .entry(prod.lhs)
                .or_insert_with(Vec::new)
                .push(prod.id.clone());
        }

        let starting_production_ids = production_ids_by_lhs
            .get(starting_term)
            .expect("starting Term has no production")
            .clone();

        Self {
            starting_production_ids,
            productions,
            production_ids_by_lhs,
        }
    }
    pub fn starting_iter(&self) -> impl Iterator<Item = &Production<'gram>> {
        self.starting_production_ids
            .iter()
            .map(|id| &self.productions[id.0])
    }
    pub fn get_production_parts_by_id(
        &self,
        prod_id: &ProductionId,
    ) -> (&'gram Term, &'gram crate::Expression) {
        self.productions
            .get(prod_id.0)
            .map(|p| (p.lhs, p.rhs))
            .expect("invalid Production ID")
    }
    pub fn get_productions_by_lhs(
        &self,
        lhs: &'gram Term,
    ) -> impl Iterator<Item = &Production<'gram>> {
        self.production_ids_by_lhs
            .get(lhs)
            .into_iter()
            .flat_map(|v| v.iter())
            .map(|id| &self.productions[id.0])
    }
}

#[derive(Debug)]
struct Terms<'gram> {
    slice: &'gram [Term],
}

impl<'gram> Terms<'gram> {
    pub fn new(slice: &'gram [Term]) -> Self {
        Self { slice }
    }
    pub fn matching(&self) -> Option<&'gram Term> {
        self.slice.get(0)
    }
    pub fn advance_by(&self, step: usize) -> &'gram [Term] {
        &self.slice[step..]
    }
}

#[derive(Clone)]
struct InputRange<'gram> {
    input: std::rc::Rc<Vec<&'gram str>>,
    start: usize,
    len: usize,
}

impl<'gram> InputRange<'gram> {
    pub fn new(input: Vec<&'gram str>) -> Self {
        let input = std::rc::Rc::new(input);
        Self {
            input,
            start: 0,
            len: 0,
        }
    }
    pub fn next(&self) -> Option<&str> {
        self.input.get(self.start + self.len).map(|i| *i)
    }
    pub fn after(&self) -> Self {
        Self {
            input: self.input.clone(),
            start: self.start + self.len,
            len: 0,
        }
    }
    pub fn advance_by(&self, step: usize) -> Self {
        let max_len = self.input.len() - self.start;
        Self {
            input: self.input.clone(),
            start: self.start,
            len: std::cmp::min(self.len + step, max_len),
        }
    }
    pub fn is_complete(&self) -> bool {
        self.start == 0 && self.len == self.input.len()
    }
    pub fn state_id(&self) -> StateId {
        StateId(self.start + self.len)
    }
}

impl<'gram> std::fmt::Debug for InputRange<'gram> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let before = &self.input[..self.start];
        let scanned = &self.input[self.start..][..self.len];
        let after = &self.input[self.start..][self.len..];
        write!(
            f,
            "InputRange({:?}, {:?}) ({:?} | {:?} | {:?})",
            self.start, self.len, before, scanned, after
        )
    }
}

#[derive(Debug, Clone, Copy)]
enum TermMatch<'gram> {
    Terminal(&'gram str),
    NonTerminal(ArenaKey),
}

#[derive(Debug)]
struct EarleyState<'gram> {
    lhs: &'gram Term,
    matched_terms: Vec<TermMatch<'gram>>,
    unmatched_terms: Terms<'gram>,
    production_id: ProductionId,
    input_range: InputRange<'gram>,
}

impl<'gram> EarleyState<'gram> {
    pub fn new(
        lhs: &'gram Term,
        production_id: ProductionId,
        unmatched_terms: &'gram [Term],
        input_range: InputRange<'gram>,
    ) -> Self {
        let matched_terms = Vec::with_capacity(0);
        let unmatched_terms = Terms::new(unmatched_terms);
        Self {
            lhs,
            matched_terms,
            unmatched_terms,
            production_id,
            input_range,
        }
    }
    pub fn new_term_match(
        state: &EarleyState<'gram>,
        matched_term: TermMatch<'gram>,
        input_range_step: usize,
    ) -> Self {
        let mut matched_terms = Vec::with_capacity(state.matched_terms.len() + 1);
        matched_terms.extend_from_slice(&state.matched_terms);
        matched_terms.push(matched_term);

        Self {
            lhs: state.lhs,
            matched_terms,
            unmatched_terms: Terms::new(state.unmatched_terms.advance_by(1)),
            production_id: state.production_id.clone(),
            input_range: state.input_range.advance_by(input_range_step),
        }
    }
    pub fn is_complete(&self, starting_prod_ids: &[ProductionId]) -> bool {
        starting_prod_ids.contains(&self.production_id) && self.input_range.is_complete()
    }
}

fn predict<'gram, 'a>(
    matching: &'gram Term,
    input_range: &'a InputRange<'gram>,
    grammar: &'a Grammar<'gram>,
) -> impl Iterator<Item = EarleyState<'gram>> + 'a {
    grammar.get_productions_by_lhs(matching).map(|prod| {
        EarleyState::new(
            prod.lhs,
            prod.id.clone(),
            &prod.rhs.terms,
            input_range.after(),
        )
    })
}

fn scan<'gram, 'a>(state: &'a EarleyState<'gram>) -> impl Iterator<Item = EarleyState<'gram>> + 'a
where
    'gram: 'a,
{
    state
        .unmatched_terms
        .matching()
        .zip(state.input_range.next())
        .and_then(|(matching, next_input)| match matching {
            Term::Terminal(term) if term == next_input => Some(term),
            _ => None,
        })
        .map(|term| {
            let term_match = TermMatch::Terminal(term);
            EarleyState::new_term_match(state, term_match, 1)
        })
        .into_iter()
}

fn complete<'gram, 'a>(
    key: ArenaKey,
    input_range: &'a InputRange<'gram>,
    parent: &'a EarleyState<'gram>,
) -> EarleyState<'gram> {
    let term_match = TermMatch::NonTerminal(key);
    EarleyState::new_term_match(parent.clone(), term_match, input_range.len)
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct StateProcessingKey {
    input_start: usize,
    input_len: usize,
    production_id: ProductionId,
    unmatched_term_len: usize,
}

impl<'gram> StateProcessingKey {
    pub fn from_state(state: &EarleyState<'gram>) -> Self {
        Self {
            input_start: state.input_range.start,
            input_len: state.input_range.len,
            production_id: state.production_id.clone(),
            unmatched_term_len: state.unmatched_terms.slice.len(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct StateMatchingKey<'gram> {
    state_id: StateId,
    term: Option<&'gram Term>,
}

impl<'gram> StateMatchingKey<'gram> {
    pub fn from_state(state: &EarleyState<'gram>) -> Self {
        let state_id = state.input_range.state_id();
        let term = state.unmatched_terms.matching();
        Self { state_id, term }
    }
    pub fn from_complete(state: &EarleyState<'gram>) -> Self {
        let state_id = StateId(state.input_range.start);
        let term = Some(state.lhs);
        Self { state_id, term }
    }
}

slotmap::new_key_type! {
    struct ArenaKey;
}

type Arena<'gram> = slotmap::SlotMap<ArenaKey, EarleyState<'gram>>;

type StateProcessingSet = std::collections::HashSet<StateProcessingKey>;

type StateMatchingMap<'gram> = std::collections::HashMap<StateMatchingKey<'gram>, Vec<ArenaKey>>;

#[derive(Default)]
struct StateArena<'gram> {
    arena: Arena<'gram>,
    unprocessed: std::collections::VecDeque<ArenaKey>,
    processed_set: StateProcessingSet,
    matching_map: StateMatchingMap<'gram>,
}

struct Unprocessed<'gram> {
    key: ArenaKey,
    matching: Option<&'gram Term>,
    input_range: InputRange<'gram>,
}

impl<'gram> StateArena<'gram> {
    pub fn new() -> Self {
        Default::default()
    }
    pub fn alloc_extend(&mut self, iter: impl Iterator<Item = EarleyState<'gram>>) {
        for state in iter {
            let state_key = StateProcessingKey::from_state(&state);
            let is_new_state = self.processed_set.insert(state_key);

            if !is_new_state {
                continue;
            }

            let matching_state_key = StateMatchingKey::from_state(&state);

            let state = self.arena.insert(state);
            self.unprocessed.push_back(state);

            if let Some(Term::Nonterminal(_)) = matching_state_key.term {
                self.matching_map
                    .entry(matching_state_key)
                    .or_insert_with(Vec::new)
                    .push(state);
            }
        }
    }
    pub fn get(&self, key: ArenaKey) -> &EarleyState<'gram> {
        self.arena.get(key).expect("invalid ArenaKey")
    }
    pub fn get_matching(
        &self,
        state: &EarleyState<'gram>,
    ) -> impl Iterator<Item = &EarleyState<'gram>> {
        let key = StateMatchingKey::from_complete(state);
        self.matching_map
            .get(&key)
            .into_iter()
            .flat_map(|keys| keys.iter())
            .map(|key| self.get(*key))
    }
    pub fn pop_unprocessed(&mut self) -> Option<Unprocessed<'gram>> {
        self.unprocessed
            .pop_front()
            .and_then(|key| self.arena.get(key).map(|state| (state, key)))
            .map(|(state, key)| Unprocessed {
                key,
                input_range: state.input_range.clone(),
                matching: state.unmatched_terms.matching(),
            })
    }
}

struct ParseIter<'gram> {
    grammar: Grammar<'gram>,
    state_arena: StateArena<'gram>,
}

impl<'gram> ParseIter<'gram> {
    pub fn new(
        grammar: &'gram crate::Grammar,
        input_iter: impl Iterator<Item = &'gram str>,
    ) -> Self {
        let grammar = Grammar::new(grammar);
        let input: Vec<_> = input_iter.collect();

        let state_arena = StateArena::new();

        let mut parse_iter = Self {
            grammar,
            state_arena,
        };

        let starting_input_range = InputRange::new(input);
        let starting_states = parse_iter.grammar.starting_iter().map(|prod| {
            EarleyState::new(
                prod.lhs,
                prod.id.clone(),
                &prod.rhs.terms,
                starting_input_range.clone(),
            )
        });

        parse_iter.state_arena.alloc_extend(starting_states);

        parse_iter
    }
    fn get_parse_tree(&self, state: &EarleyState<'gram>) -> ParseTree<'gram> {
        let (lhs, _) = self
            .grammar
            .get_production_parts_by_id(&state.production_id);

        let rhs = state
            .matched_terms
            .iter()
            .map(|child| match child {
                TermMatch::Terminal(term) => ParseTreeMatch::Terminal(term),
                TermMatch::NonTerminal(key) => {
                    let state = self.state_arena.get(*key);
                    ParseTreeMatch::Nonterminal(self.get_parse_tree(state))
                }
            })
            .collect();

        let parse_tree = ParseTree { lhs, rhs };
        parse_tree
    }
}

impl<'gram> Iterator for ParseIter<'gram> {
    type Item = ParseTree<'gram>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(Unprocessed {
            key,
            matching,
            input_range,
        }) = self.state_arena.pop_unprocessed()
        {
            match matching {
                // predict
                Some(matching @ Term::Nonterminal(_)) => {
                    // no need to predict for more input if input is complete
                    if input_range.is_complete() {
                        break;
                    }
                    let predictions = predict(matching, &input_range, &self.grammar);
                    self.state_arena.alloc_extend(predictions);
                }
                // scan
                Some(Term::Terminal(_)) => {
                    let state = self.state_arena.get(key);
                    // TODO: can the output vector be reused?
                    let scanned = scan(state).collect::<Vec<_>>();
                    self.state_arena.alloc_extend(scanned.into_iter());
                }
                // complete
                None => {
                    let state = self.state_arena.get(key);
                    if state.is_complete(&self.grammar.starting_production_ids) {
                        let parse_tree = self.get_parse_tree(state);
                        return Some(parse_tree);
                    }

                    let completed = self
                        .state_arena
                        .get_matching(state)
                        .map(|parent| complete(key, &input_range, parent))
                        .collect::<Vec<_>>();

                    self.state_arena.alloc_extend(completed.into_iter());
                }
            }
        }
        None
    }
}

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input_iter: impl Iterator<Item = &'gram str>,
) -> impl Iterator<Item = ParseTree<'_>> {
    ParseIter::new(grammar, input_iter)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;

    #[test]
    fn parse_dna_left_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <dna> <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "G A T T A C A".split_whitespace();

        let parses: Vec<_> = parse(&grammar, input).collect();
        assert_eq!(parses.len(), 1);
    }

    #[test]
    fn parse_dna_right_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "G A T T A C A".split_whitespace();

        let parses: Vec<_> = parse(&grammar, input).collect();
        assert_eq!(parses.len(), 1);
    }

    #[test]
    fn parse_ambiguous() {
        let grammar: Grammar = "<start> ::= <a> | <b>
        <a> ::= \"END\"
        <b> ::= \"END\""
            .parse()
            .unwrap();

        let input = "END".split_whitespace();

        let parses: Vec<_> = parse(&grammar, input).collect();
        assert_eq!(parses.len(), 2);
    }

    #[test]
    // (source: https://loup-vaillant.fr/tutorials/earley-parsing/recogniser)
    // Sum     -> Sum     [+-] Product
    // Sum     -> Product
    // Product -> Product [*/] Factor
    // Product -> Factor
    // Factor  -> '(' Sum ')'
    // Factor  -> Number
    // Number  -> [0-9] Number
    // Number  -> [0-9]
    fn parse_math() {
        let grammar: Grammar = "<sum> ::= <sum> <add> <product>
            <sum> ::= <product>
            <product> ::= <product> <mult> <factor>
            <product> ::= <factor>
            <add> ::= \"+\" | \"-\"
            <mult> ::= \"*\" | \"/\"
            <factor> ::= \"(\" <sum> \")\"
            <factor> ::= <number>
            <number> ::= <digit> <number>
            <number> ::= <digit>
            <digit> ::= \"0\" | \"1\" | \"2\" | \"3\" | \"4\" | \"5\" | \"6\" | \"7\" | \"8\" | \"9\"
        ".parse().unwrap();

        let input = "1 + ( 2 * 3 - 4 )".split_whitespace();

        let parses: Vec<_> = parse(&grammar, input).collect();
        assert_eq!(parses.len(), 1);
        println!("{}", parses[0]);
    }
}

/* NEXT
 * what should failure modes of parsing look like? Result<Iter> ? what error context can be included ?
 * unit tests
 * property test (gen random walk, should be parseable)
 * grammar::parse
 * perf testing
 * DOCS
 * clippy
 */
