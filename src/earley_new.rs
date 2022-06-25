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

type TermIter<'gram> = crate::expression::Iter<'gram>;

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
        self.len == self.input.len()
    }
    pub fn bound(&self) -> (usize, usize) {
        (self.start, self.len)
    }
}

impl<'gram> std::fmt::Debug for InputRange<'gram> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let before = &self.input[..self.start];
        let scanned = &self.input[self.start..][..self.len];
        let after = &self.input[self.start..][self.len..];
        write!(f, "InputRange ({:?} | {:?} | {:?})", before, scanned, after)
    }
}

#[derive(Debug)]
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
        production_id: ProductionId,
        mut unmatched: TermIter<'gram>,
        input_range: InputRange<'gram>,
    ) -> Self {
        let matching = unmatched.next();
        Self {
            lhs,
            matching,
            unmatched,
            production_id,
            input_range,
        }
    }
}

fn predict<'gram>(
    state: &'gram EarleyState<'gram>,
    grammar: &'gram Grammar,
) -> impl Iterator<Item = EarleyState<'gram>> {
    state
        .matching
        .into_iter()
        .flat_map(|matching| grammar.get_productions_by_lhs(matching))
        .map(|prod| {
            EarleyState::new(
                prod.lhs,
                prod.id.clone(),
                prod.rhs.terms_iter(),
                state.input_range.after(),
            )
        })
}

fn scan<'gram>(state: &'gram EarleyState<'gram>) -> impl Iterator<Item = EarleyState<'gram>> {
    state
        .matching
        .zip(state.input_range.next())
        .into_iter()
        .filter(|(matching, next_input)| match *matching {
            Term::Nonterminal(_) => false,
            Term::Terminal(term) => term == *next_input,
        })
        .map(|_| {
            EarleyState::new(
                state.lhs,
                state.production_id.clone(),
                state.unmatched.clone(),
                state.input_range.advance_by(1),
            )
        })
}

fn complete<'gram>(
    state: &'gram EarleyState<'gram>,
    parent: &'gram EarleyState<'gram>,
) -> EarleyState<'gram> {
    let foo = EarleyState::new(
        parent.lhs,
        parent.production_id.clone(),
        parent.unmatched.clone(),
        parent.input_range.advance_by(state.input_range.len),
    );
    println!("FOO: {:?}", foo);
    foo
}

type Arena<'gram> = typed_arena::Arena<EarleyState<'gram>>;
type StateProcessingKey = ((usize, usize), ProductionId);
type StateProcessingSet = std::collections::HashSet<StateProcessingKey>;
type StateMatchingKey<'gram> = (usize, Option<&'gram Term>);
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
            let state_key = (state.input_range.bound(), state.production_id.clone());
            let is_new_state = this.processed_set.insert(state_key);

            if !is_new_state {
                println!("deduped: {:?}", state);
                continue;
            }

            let state = this.arena.alloc(state);
            println!("new: {:?}", state);
            allocated.push(state as &_);
            this.unprocessed.push(state);

            let matching_state_key: StateMatchingKey = (state.input_range.start, state.matching);
            this.matching_map
                .entry(matching_state_key)
                .or_insert_with(Vec::new)
                .push(state);
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
        let key = (state.input_range.start, Some(state.lhs));
        this.matching_map
            .get(&key)
            .into_iter()
            .flat_map(|ptrs| ptrs.iter())
            .map(|ptr| unsafe { &**ptr as &'gram _ })
            .map(|state| {
                println!("matching? {:?}", state);
                state
            })
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
            prod.rhs.terms_iter(),
            starting_input_range.clone(),
        )
    });
    let _ = state_arena.as_mut().alloc_extend(starting_states);

    while let Some(state) = state_arena.as_mut().pop_unprocessed() {
        println!("state: {:?}", state);
        match state.matching {
            // predict
            Some(Term::Nonterminal(_)) => {
                println!("predict!");
                let predictions = predict(state, &grammar);
                let _ = state_arena.as_mut().alloc_extend(predictions);
            }
            // scan
            Some(Term::Terminal(_)) => {
                println!("scan!");
                let scanned = scan(state);
                let _ = state_arena.as_mut().alloc_extend(scanned);
            }
            // complete
            None => {
                // TODO: BROKEN!
                println!("complete!");
                let matching = state_arena.as_mut().get_matching(state);
                let completed = matching
                    .map(|parent| complete(state, parent))
                    .collect::<Vec<_>>();

                let completed = state_arena.as_mut().alloc_extend(completed.into_iter());

                let full_input_parses = completed
                    .filter(|state| state.input_range.is_complete())
                    // TODO: actual parse tree info!
                    .map(|_| crate::grammar::ParseTree {});

                parses.extend(full_input_parses);
            }
        }
    }

    println!("{:?}", parses);
    parses.into_iter()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;

    #[test]
    fn parse_dna_left_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "G A T T A C A".split_whitespace();

        let mut parses = parse(&grammar, input);
        assert!(matches!(parses.next(), Some(_)));
    }
}
