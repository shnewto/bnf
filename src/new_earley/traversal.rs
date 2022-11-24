use super::grammar::{
    GrammarMatching, Production, ProductionId, ProductionMatch, ProductionMatching, TermMatch,
};
use super::input_range::{InputRange, InputRangeOffset};
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
        let input_range = input_range.after();
        let matching = prod.start_matching();
        Self {
            matching,
            input_range,
        }
    }
    pub fn duplicate_key(&self) -> TraversalDuplicateKey {
        TraversalDuplicateKey {
            input_range: self.input_range.offset.clone(),
            prod_id: self.matching.prod_id,
            matched_term_count: self.matching.matched_count(),
        }
    }
    pub fn earley(&self) -> EarleyStep<'gram> {
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
        for traversal in traversals {
            let processed_key = traversal.duplicate_key();
            let is_new_traversal = self.processed.insert(processed_key);
            let prefix = if is_new_traversal { "NEW" } else { "DUPE" };
            let processed_key = traversal.duplicate_key();
            println!("{prefix} {processed_key:#?} {traversal:#?}");

            if !is_new_traversal {
                continue;
            }

            self.queue.push_back(traversal);
        }
    }

    pub fn handle_pop<H, I>(&mut self, mut handler: H) -> Option<ProductionMatch<'gram>>
    where
        I: Iterator<Item = Traversal<'gram>>,
        H: FnMut(Traversal<'gram>) -> I,
    {
        while let Some(traversal) = self.queue.pop_front() {
            let is_full_traversal = traversal.input_range.is_complete()
                && self.starting_prod_ids.contains(&traversal.matching.prod_id);

            let full_prod_match = if is_full_traversal {
                traversal.matching.complete()
            } else {
                None
            };

            let new_traversals = handler(traversal);
            self.extend(new_traversals);

            if let Some(prod_match) = full_prod_match {
                return Some(prod_match);
            }
        }

        None
    }
}
