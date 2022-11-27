use super::grammar::{
    GrammarMatching, Production, ProductionId, ProductionMatch, ProductionMatching, TermMatch,
};
use super::input_range::{InputRange, InputRangeOffset};
use crate::{
    append_vec::{append_only_vec_id, AppendOnlyVec},
    tracing, Term,
};
use std::collections::{HashSet, VecDeque};

pub(crate) enum EarleyStep<'gram> {
    Predict(&'gram Term),
    Scan(&'gram String),
    Complete(ProductionMatch<'gram>),
}

append_only_vec_id!(pub(crate) TraversalId);

#[derive(Debug)]
pub(crate) struct Traversal<'gram> {
    pub input_range: InputRange<'gram>,
    pub matching: ProductionMatching<'gram>,
}

impl<'gram> Traversal<'gram> {
    pub fn start_production(prod: &Production<'gram>, input_range: &InputRange<'gram>) -> Self {
        let _span = tracing::span!(tracing::Level::TRACE, "start_production").entered();
        let input_range = input_range.after();
        let matching = prod.start_matching();
        Self {
            matching,
            input_range,
        }
    }
    pub fn duplicate_key(&self) -> TraversalDuplicateKey {
        let _span = tracing::span!(tracing::Level::TRACE, "duplicate_key").entered();
        TraversalDuplicateKey {
            input_range: self.input_range.offset.clone(),
            prod_id: self.matching.prod_id,
            matched_term_count: self.matching.matched_count(),
        }
    }
    pub fn earley(&self) -> EarleyStep<'gram> {
        let _span = tracing::span!(tracing::Level::TRACE, "earley").entered();
        match self.matching.next() {
            None => {
                let prod_match = self
                    .matching
                    .complete()
                    .expect("matching must be complete because no next term");
                EarleyStep::Complete(prod_match)
            }
            Some(term) => match term {
                Term::Nonterminal(_) => EarleyStep::Predict(term),
                Term::Terminal(term) => EarleyStep::Scan(term),
            },
        }
    }
    pub fn match_term(&self, term_match: TermMatch<'gram>) -> Option<Self> {
        let _span = tracing::span!(tracing::Level::TRACE, "match_term").entered();
        let input_len = match &term_match {
            TermMatch::Terminal(term) => term.len(),
            TermMatch::Nonterminal(prod) => prod.input_len,
        };

        self.matching.match_term(term_match).map(|matching| {
            let input_range = self.input_range.advance_by(input_len);

            Self {
                input_range,
                matching,
            }
        })
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct TraversalDuplicateKey {
    input_range: InputRangeOffset,
    prod_id: ProductionId,
    matched_term_count: usize,
}

#[derive(Debug, Default)]
pub(crate) struct TraversalCompletionQueue<'gram> {
    arena: AppendOnlyVec<Traversal<'gram>, TraversalId>,
    queue: VecDeque<TraversalId>,
    processed: HashSet<TraversalDuplicateKey>,
}

impl<'gram> TraversalCompletionQueue<'gram> {
    pub fn new(grammar: &GrammarMatching<'gram>, input_range: InputRange<'gram>) -> Self {
        let queue = VecDeque::new();
        let starting_traversals = grammar
            .starting_productions()
            .map(|prod| Traversal::start_production(prod, &input_range));

        let mut traversal_queue = Self {
            queue,
            ..Default::default()
        };

        traversal_queue.extend(starting_traversals);

        traversal_queue
    }

    fn extend<I>(&mut self, traversals: I)
    where
        I: Iterator<Item = Traversal<'gram>>,
    {
        let _span = tracing::span!(tracing::Level::TRACE, "Queue::extend").entered();
        for traversal in traversals {
            let processed_key = traversal.duplicate_key();
            let is_new_traversal = self.processed.insert(processed_key);

            if !is_new_traversal {
                continue;
            }

            let id = self.arena.push(traversal);
            self.queue.push_back(id);
        }
    }

    pub fn handle_pop<H>(&mut self, mut handler: H) -> Option<ProductionMatch<'gram>>
    where
        H: FnMut(
            TraversalId,
            &AppendOnlyVec<Traversal<'gram>, TraversalId>,
            &mut Vec<Traversal<'gram>>,
        ) -> Option<ProductionMatch<'gram>>,
    {
        let _span = tracing::span!(tracing::Level::TRACE, "Queue::handle_pop").entered();
        let pop = |queue: &mut VecDeque<TraversalId>| -> Option<TraversalId> {
            let _span = tracing::span!(tracing::Level::TRACE, "Queue::pop").entered();
            queue.pop_front()
        };
        let mut created = Vec::<Traversal>::new();
        let _outer = tracing::span!(tracing::Level::TRACE, "Queue::outer_while_let").entered();
        while let Some(id) = pop(&mut self.queue) {
            let _inner = tracing::span!(tracing::Level::TRACE, "Queue::inner_while_let").entered();
            let prod_match = handler(id, &self.arena, &mut created);
            self.extend(created.drain(..));

            if prod_match.is_some() {
                return prod_match;
            }
        }

        None
    }
}
