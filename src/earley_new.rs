// DESIGN
// PREDICT
// ProductionWithId BY LHS -> MANY EarleyState
//
// SCAN
// &str -> 0/1 EarleyState
//
// COMPLETE
// EarleyStates BY (start state id, matching) -> MANY EarleyState
//
// SUCCESS
// EarleyStates BY (end state id, start state id, matching)
// OR
// when COMPLETE, if start = 0, and end = end, add to successes
use crate::Term;
use std::pin::Pin;

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
    starting_term: &'gram Term,
    productions_by_lhs: std::collections::HashMap<&'gram Term, Vec<Production<'gram>>>,
}

impl<'gram> Grammar<'gram> {
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
        let starting_term = &grammar.productions_iter().next().unwrap().lhs;
        let productions = grammar
            .productions_iter()
            .flat_map(|prod| prod.rhs_iter().map(|rhs| (&prod.lhs, rhs)))
            .enumerate()
            .map(|(id, (lhs, rhs))| {
                let id = ProductionId(id);
                (lhs, Production { id, lhs, rhs })
            });

        let mut productions_by_lhs = std::collections::HashMap::new();

        for (lhs, prod) in productions {
            productions_by_lhs
                .entry(lhs)
                .or_insert_with(Vec::new)
                .push(prod);
        }

        Self {
            starting_term,
            productions_by_lhs,
        }
    }
    pub fn starting_iter(&self) -> impl Iterator<Item = &Production<'gram>> {
        self.productions_by_lhs
            .get(self.starting_term)
            .into_iter()
            .flat_map(|v| v.iter())
    }
    pub fn get_productions_by_lhs(
        &self,
        lhs: &'gram Term,
    ) -> impl Iterator<Item = &Production<'gram>> {
        self.productions_by_lhs
            .get(lhs)
            .into_iter()
            .flat_map(|v| v.iter())
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
    input: &'gram [&'gram str],
    start: usize,
    len: usize,
}

impl<'gram> InputRange<'gram> {
    pub fn new(input: &'gram [&'gram str]) -> Self {
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
            input: self.input,
            start: self.start + self.len,
            len: 0,
        }
    }
    pub fn advance_by(&self, step: usize) -> Self {
        let max_len = self.input.len() - self.start;
        Self {
            input: self.input,
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

#[derive(Debug, Clone)]
enum TermMatch<'gram> {
    Terminal(&'gram str),
    NonTerminal(&'gram EarleyState<'gram>),
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
        let matched_terms = Vec::with_capacity(unmatched_terms.len());
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
        state: &'gram EarleyState<'gram>,
        matched_term: TermMatch<'gram>,
        input_range_step: usize,
    ) -> Self {
        let mut matched_terms = state.matched_terms.clone();
        matched_terms.push(matched_term);
        Self {
            lhs: state.lhs,
            matched_terms,
            unmatched_terms: Terms::new(state.unmatched_terms.advance_by(1)),
            production_id: state.production_id.clone(),
            input_range: state.input_range.advance_by(input_range_step),
        }
    }
}

fn predict<'gram>(
    state: &'gram EarleyState<'gram>,
    grammar: &'gram Grammar,
) -> impl Iterator<Item = EarleyState<'gram>> {
    state
        .unmatched_terms
        .matching()
        .into_iter()
        .flat_map(|matching| grammar.get_productions_by_lhs(matching))
        .map(|prod| {
            EarleyState::new(
                prod.lhs,
                prod.id.clone(),
                &prod.rhs.terms,
                state.input_range.after(),
            )
        })
}

fn scan<'gram>(state: &'gram EarleyState<'gram>) -> impl Iterator<Item = EarleyState<'gram>> {
    state
        .unmatched_terms
        .matching()
        .zip(state.input_range.next())
        .and_then(|(matching, next_input)| match matching {
            Term::Terminal(term) if term == next_input => Some(next_input),
            _ => None,
        })
        .map(|term| {
            let term_match = TermMatch::Terminal(&term);
            EarleyState::new_term_match(state, term_match, 1)
        })
        .into_iter()
}

fn complete<'gram>(
    state: &'gram EarleyState<'gram>,
    parent: &'gram EarleyState<'gram>,
) -> EarleyState<'gram> {
    let term_match = TermMatch::NonTerminal(state);
    EarleyState::new_term_match(parent, term_match, state.input_range.len)
}

type Arena<'gram> = typed_arena::Arena<EarleyState<'gram>>;
#[derive(Debug, PartialEq, Eq, Hash)]
struct StateProcessingKey {
    state_id: StateId,
    production_id: ProductionId,
    unmatched_term_len: usize,
}

impl<'gram> StateProcessingKey {
    pub fn from_state(state: &EarleyState<'gram>) -> Self {
        Self {
            state_id: state.input_range.state_id(),
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

type StateProcessingSet = std::collections::HashSet<StateProcessingKey>;

type StateMatchingMap<'gram> =
    std::collections::HashMap<StateMatchingKey<'gram>, Vec<*const EarleyState<'gram>>>;

#[derive(Default)]
struct StateArena<'gram> {
    arena: Arena<'gram>,
    unprocessed: Vec<*const EarleyState<'gram>>,
    processed_set: StateProcessingSet,
    matching_map: StateMatchingMap<'gram>,
}

impl<'gram> StateArena<'gram> {
    pub fn new() -> Self {
        Default::default()
    }
    pub fn alloc_extend(
        self: Pin<&mut Self>,
        iter: impl Iterator<Item = EarleyState<'gram>>,
    ) -> impl Iterator<Item = &EarleyState<'gram>> {
        // SAFETY: must not "move" any data out of `self`
        // because would corrupt self referential fields
        let this = unsafe { self.get_unchecked_mut() };
        let mut allocated = vec![];

        for state in iter {
            let state_key = StateProcessingKey::from_state(&state);
            let is_new_state = this.processed_set.insert(state_key);

            if !is_new_state {
                continue;
            }

            let state = this.arena.alloc(state);
            allocated.push(state as &_);
            this.unprocessed.push(state);

            if let Some(Term::Nonterminal(_)) = state.unmatched_terms.matching() {
                let matching_state_key = StateMatchingKey::from_state(&state);
                this.matching_map
                    .entry(matching_state_key)
                    .or_insert_with(Vec::new)
                    .push(state);
            }
        }

        allocated.into_iter()
    }
    pub fn pop_unprocessed(self: Pin<&mut Self>) -> Option<&'gram EarleyState<'gram>> {
        let this = unsafe { self.get_unchecked_mut() };
        this.unprocessed.pop().map(|i| unsafe { &*i })
    }
    pub fn get_matching<'a>(
        self: Pin<&'a mut Self>,
        state: &'gram EarleyState<'gram>,
    ) -> impl Iterator<Item = &'gram EarleyState<'gram>> + 'a {
        let this = unsafe { self.get_unchecked_mut() };
        let key = StateMatchingKey::from_complete(state);
        this.matching_map
            .get(&key)
            .into_iter()
            .flat_map(|ptrs| ptrs.iter())
            .map(|ptr| unsafe { &**ptr as &'gram _ })
    }
}

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input_iter: impl Iterator<Item = &'gram str>,
) -> impl Iterator<Item = crate::grammar::ParseTree> {
    let grammar = Grammar::new(grammar);
    let input: Vec<_> = input_iter.collect();
    let mut parses = Vec::<crate::grammar::ParseTree>::new();

    // SAFETY: shadow the pinned variable so it may only be accessed at its pinned location
    // also because it is pinned on "the stack", state_set cannot be returned
    let mut state_arena = StateArena::new();
    let mut state_arena = unsafe { std::pin::Pin::new_unchecked(&mut state_arena) };

    let starting_input_range = InputRange::new(&input);
    let starting_states = grammar.starting_iter().map(|prod| {
        EarleyState::new(
            prod.lhs,
            prod.id.clone(),
            &prod.rhs.terms,
            starting_input_range.clone(),
        )
    });
    let _ = state_arena.as_mut().alloc_extend(starting_states);

    while let Some(state) = state_arena.as_mut().pop_unprocessed() {
        match state.unmatched_terms.matching() {
            // predict
            Some(Term::Nonterminal(_)) => {
                let predictions = predict(state, &grammar);
                let _ = state_arena.as_mut().alloc_extend(predictions);
            }
            // scan
            Some(Term::Terminal(_)) => {
                let scanned = scan(state);
                let _ = state_arena.as_mut().alloc_extend(scanned);
            }
            // complete
            None => {
                let matching = state_arena.as_mut().get_matching(state);
                let completed = matching
                    .map(|parent| complete(state, parent))
                    .collect::<Vec<_>>();

                let completed = state_arena.as_mut().alloc_extend(completed.into_iter());

                let full_input_parses = completed
                    .filter(|state| state.input_range.is_complete())
                    // TODO: actual parse tree info!
                    .map(|_| {
                        println!("** {:?} {:#?}", state.input_range, state);
                        crate::grammar::ParseTree {}
                    });

                parses.extend(full_input_parses);
            }
        }
    }

    parses.into_iter()
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

        let mut parses = parse(&grammar, input);
        assert!(matches!(parses.next(), Some(_)));
    }
}
