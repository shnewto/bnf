use super::grammar::{
    GrammarMatching, Production, ProductionId, ProductionMatch, ProductionMatching, TermMatch,
};
use super::input_range::{InputRange, InputRangeOffset};
use crate::tracing;
use crate::Term;
use std::collections::{HashSet, VecDeque};

pub(crate) enum EarleyStep<'gram> {
    Predict(&'gram Term),
    Scan(&'gram String),
    Complete(ProductionMatch<'gram>),
}

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
    queue: VecDeque<Traversal<'gram>>,
    processed: HashSet<TraversalDuplicateKey>,
    starting_prod_ids: HashSet<ProductionId>,
}

impl<'gram> TraversalCompletionQueue<'gram> {
    pub fn new(grammar: &GrammarMatching<'gram>, input_range: InputRange<'gram>) -> Self {
        let queue = VecDeque::new();
        let starting_traversals = grammar
            .starting_productions()
            .map(|prod| Traversal::start_production(prod, &input_range));

        let starting_prod_ids = grammar.starting_productions().map(|prod| prod.id).collect();

        let mut traversal_queue = Self {
            queue,
            starting_prod_ids,
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

            self.queue.push_back(traversal);
        }
    }

    pub fn handle_pop<H>(&mut self, mut handler: H) -> Option<ProductionMatch<'gram>>
    where
        H: FnMut(Traversal<'gram>, &mut Vec<Traversal<'gram>>),
    {
        let _span = tracing::span!(tracing::Level::TRACE, "Queue::handle_pop").entered();
        let pop = |queue: &mut VecDeque<Traversal<'gram>>| -> Option<Traversal> {
            let _span = tracing::span!(tracing::Level::TRACE, "Queue::pop").entered();
            queue.pop_front()
        };
        let mut created = Vec::<Traversal>::new();
        let _outer = tracing::span!(tracing::Level::TRACE, "Queue::outer_while_let").entered();
        while let Some(traversal) = pop(&mut self.queue) {
            let _inner = tracing::span!(tracing::Level::TRACE, "Queue::inner_while_let").entered();
            let full_prod_match = {
                let _span = tracing::span!(tracing::Level::TRACE, "full_prod_match").entered();
                let is_full_traversal = traversal.input_range.is_complete()
                    && self.starting_prod_ids.contains(&traversal.matching.prod_id);
                if is_full_traversal {
                    traversal.matching.complete()
                } else {
                    None
                }
            };

            {
                let _span = tracing::span!(tracing::Level::TRACE, "new_traversals").entered();
                handler(traversal, &mut created);
                self.extend(created.drain(..));
            }

            {
                let _span = tracing::span!(tracing::Level::TRACE, "return").entered();
                if let Some(prod_match) = full_prod_match {
                    return Some(prod_match);
                }
            }
            drop(_inner);
        }

        drop(_outer);
        drop(_span);
        None
    }
}
