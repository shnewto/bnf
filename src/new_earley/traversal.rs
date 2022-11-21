use super::grammar::{MatchingGrammar, MatchingProduction, MatchingTerm, Production, ProductionId};
use super::input_range::{InputRange, InputRangeOffset};
use crate::append_vec::{append_only_vec_id, AppendOnlyVec};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug)]
pub(crate) struct Traversal<'gram> {
    lhs: &'gram crate::Term,
    matching: MatchingProduction<'gram>,
    input_range: InputRange<'gram>,
}

impl<'gram> Traversal<'gram> {
    pub fn start_production(prod: &Production<'gram>, input_range: &InputRange<'gram>) -> Self {
        let input_range = input_range.clone();
        let matching = prod.start_matching();
        Self {
            lhs: prod.lhs,
            matching,
            input_range,
        }
    }
    pub fn duplicate_key(&self) -> TraversalDuplicateKey {
        TraversalDuplicateKey {
            input_range: self.input_range.offset.clone(),
            prod_id: self.matching.prod_id,
            unmatched_term_len: self.matching.unmatched().len(),
        }
    }
    pub fn completion_key(&self) -> Option<TraversalCompletionKey> {
        self.matching().map(|matching| TraversalCompletionKey {
            input_range: self.input_range.offset.clone(),
            matching,
        })
    }
    pub fn matching(&self) -> Option<&'gram crate::Term> {
        self.matching.matching().and_then(|term| match term {
            MatchingTerm::Matched(_) => None,
            MatchingTerm::Unmatched(term) => Some(*term),
        })
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct TraversalDuplicateKey {
    input_range: InputRangeOffset,
    prod_id: ProductionId,
    unmatched_term_len: usize,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct TraversalCompletionKey<'gram> {
    input_range: InputRangeOffset,
    matching: &'gram crate::Term,
}

#[derive(Debug, Default)]
pub(crate) struct TraversalCompletionQueue<'gram> {
    queue: VecDeque<Traversal<'gram>>,
    processed: HashSet<TraversalDuplicateKey>,
    starting_prod_ids: HashSet<ProductionId>,
}

impl<'gram> TraversalCompletionQueue<'gram> {
    pub fn new(grammar: &MatchingGrammar<'gram>, input_range: InputRange<'gram>) -> Self {
        let mut queue = VecDeque::new();
        let starting_traversals = grammar
            .starting_productions()
            .map(|prod| Traversal::start_production(prod, &input_range));

        let starting_prod_ids = grammar.starting_productions().map(|prod| prod.id).collect();

        queue.extend(starting_traversals);

        let traversal_queue = Self {
            queue,
            starting_prod_ids,
            ..Default::default()
        };

        traversal_queue
    }

    fn extend<I>(&mut self, traversals: I)
    where
        I: Iterator<Item = Traversal<'gram>>,
    {
        for traversal in traversals {
            let processed_key = traversal.duplicate_key();
            let is_new_traversal = self.processed.insert(processed_key);

            if !is_new_traversal {
                continue;
            }

            let completion_key = traversal.completion_key();
            self.queue.push_back(traversal);
        }
    }

    pub fn process<H, I>(&mut self, handler: H) -> Option<Traversal<'gram>>
    where
        I: Iterator<Item = Traversal<'gram>>,
        H: Fn(&Traversal<'gram>) -> I,
    {
        while let Some(traversal) = self.queue.pop_front() {
            {
                let new_traversals = handler(&traversal);
                self.extend(new_traversals);
            }

            if traversal.input_range.is_complete()
                && self.starting_prod_ids.contains(&traversal.matching.prod_id)
            {
                return Some(traversal);
            }
        }

        None
    }
}
