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

struct Production<'gram> {
    id: ProductionId,
    lhs: &'gram Term,
    rhs: &'gram crate::Expression,
}

struct Grammar<'gram> {
    productions_by_lhs: std::collections::HashMap<&'gram Term, Vec<Production<'gram>>>,
}

impl<'gram> Grammar<'gram> {
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
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

        Self { productions_by_lhs }
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

type TermIter<'gram> = crate::expression::Iter<'gram>;

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
        todo!()
    }
    pub fn scanned(&self) -> &[&str] {
        &self.input[self.start..][..self.len]
    }
    pub fn after(&self) -> Self {
        Self {
            input: self.input,
            start: self.len,
            len: 0,
        }
    }
    pub fn advance(&self) -> Self {
        Self {
            input: self.input,
            start: self.start,
            len: self.len + 1,
        }
    }
    pub fn is_complete(&self) -> bool {
        self.len == self.input.len()
    }
}

struct EarleyState<'gram> {
    lhs: &'gram Term,
    matching: Option<&'gram Term>,
    unmatched: TermIter<'gram>,
    production_id: ProductionId,
    input_range: InputRange<'gram>,
}

impl<'gram> EarleyState<'gram> {
    pub fn new(
        lhs: &'gram Term,
        mut unmatched: TermIter<'gram>,
        input_range: InputRange<'gram>,
    ) -> Self {
        let matching = unmatched.next();
        Self {
            lhs,
            matching,
            unmatched,
            production_id: ProductionId(0),
            input_range,
        }
    }
}

fn predict<'gram>(
    state: &'gram EarleyState<'gram>,
    grammar: &'gram Grammar,
) -> impl Iterator<Item = EarleyState<'gram>> {
    std::iter::empty()
}

fn scan<'gram>(state: &'gram EarleyState<'gram>) -> impl Iterator<Item = EarleyState<'gram>> {
    std::iter::empty()
}

fn complete<'gram>(
    state: &'gram EarleyState<'gram>,
    matching_states: impl Iterator<Item = &'gram EarleyState<'gram>>,
) -> impl Iterator<Item = EarleyState<'gram>> {
    std::iter::empty()
}

type Arena<'gram> = typed_arena::Arena<EarleyState<'gram>>;
// type ArenaId<'gram> = id_arena::Id<EarleyState<'gram>>;
type StateProcessingKey = (usize, ProductionId);
type StateProcessingSet = std::collections::HashSet<StateProcessingKey>;
type StateMatchingKey<'gram> = (usize, Option<&'gram Term>);
type StateMatchingMap<'gram> =
    std::collections::HashMap<StateMatchingKey<'gram>, Vec<*const EarleyState<'gram>>>;

fn add_states<'gram>(
    arena: &'gram Arena<'gram>,
    states_by_matching: &mut StateMatchingMap<'gram>,
    processed_state_keys: &mut StateProcessingSet,
    new_states: impl Iterator<Item = EarleyState<'gram>>,
) {
    for state in new_states {
        let state_key = (state.input_range.start, state.production_id);
        let is_new_state = processed_state_keys.insert(state_key);

        if !is_new_state {
            continue;
        }

        let state = arena.alloc(state);

        let matching_state_key: StateMatchingKey = (state.input_range.start, state.matching);
        states_by_matching
            .entry(matching_state_key)
            .or_insert_with(Vec::new)
            .push(state);
    }
}

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
    pub fn alloc_extend(self: Pin<&mut Self>, iter: impl Iterator<Item = EarleyState<'gram>>) {
        // SAFETY: must not "move" any data out of `self`
        // because would corrupt self referential fields
        let this = unsafe { self.get_unchecked_mut() };

        for state in iter {
            let state_key = (state.input_range.start, state.production_id);
            let is_new_state = this.processed_set.insert(state_key);

            if !is_new_state {
                continue;
            }

            let state = this.arena.alloc(state);

            this.unprocessed.push(state);

            let matching_state_key: StateMatchingKey = (state.input_range.start, state.matching);
            this.matching_map
                .entry(matching_state_key)
                .or_insert_with(Vec::new)
                .push(state);
        }
    }
    pub fn pop_unprocessed(self: Pin<&mut Self>) -> Option<&'gram EarleyState<'gram>> {
        let this = unsafe { self.get_unchecked_mut() };
        this.unprocessed.pop().map(|i| unsafe { &*i })
    }
    pub fn get_by_matching(
        self: Pin<&mut Self>,
        state: &EarleyState<'gram>,
    ) -> impl Iterator<Item = &'gram EarleyState<'gram>> {
        std::iter::empty()
    }
}

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input_iter: impl Iterator<Item = &'gram str>,
) -> impl Iterator<Item = crate::grammar::ParseTree> {
    let grammar = Grammar::new(grammar);

    // SAFETY: shadow the pinned variable so it may only be accessed at its pinned location
    // also because it is pinned on "the stack", state_set cannot be returned
    let mut state_arena = StateArena::new();
    let mut state_arena = unsafe { std::pin::Pin::new_unchecked(&mut state_arena) };

    // TODO: init with all of the "first" production rules

    while let Some(state) = state_arena.as_mut().pop_unprocessed() {
        match state.matching {
            // predict
            Some(Term::Nonterminal(_)) => {
                let predictions = predict(state, &grammar);
                state_arena.as_mut().alloc_extend(predictions);
            }
            // scan
            Some(Term::Terminal(_)) => {
                let scanned = scan(state);
                state_arena.as_mut().alloc_extend(scanned);
            }
            // complete
            None => {
                let matching_states = state_arena.as_mut().get_by_matching(state);
                let completed = complete(state, matching_states);
                state_arena.as_mut().alloc_extend(completed);
            }
        }
    }

    // TODO: query completed with full input range!

    std::iter::empty()
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

        let input = "G A T A C A".split_whitespace();

        let mut parses = parse(&grammar, input);
        assert!(matches!(parses.next(), Some(_)));
    }
}
