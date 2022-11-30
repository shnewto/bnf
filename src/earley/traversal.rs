use super::grammar::{
    GrammarMatching, Production, ProductionId, ProductionMatch, ProductionMatching, TermMatch,
};
use super::input_range::{InputRange, InputRangeOffset};
use crate::{
    append_vec::{append_only_vec_id, AppendOnlyVec},
    tracing, Term,
};
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// The three main steps of the "Earley" parsing algorithm
#[derive(Debug)]
pub(crate) enum EarleyStep<'gram> {
    /// If the next [`crate::Term`] is [`crate::Term::Nonterminal`] then "predict" more [`Traversal`]s
    Predict(&'gram Term),
    /// If the next [`crate::Term`] is [`crate::Term::Terminal`] then "scan" input text
    Scan(&'gram String),
    /// If the [`ProductionMatching`] has no unmatched [`crate::Term`]s then "complete" pending [`Traversal`]s
    Complete(Rc<ProductionMatch<'gram>>),
}

append_only_vec_id!(pub(crate) TraversalId);

/// A step in traversing a [`crate::Grammar`]
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
                EarleyStep::Complete(Rc::new(prod_match))
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

        self.matching.add_term_match(term_match).map(|matching| {
            let input_range = self.input_range.advance_by(input_len);

            Self {
                input_range,
                matching,
            }
        })
    }
}

/// Key used for ignoring duplicate [`Traversal`]s
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct TraversalDuplicateKey {
    input_range: InputRangeOffset,
    prod_id: ProductionId,
    matched_term_count: usize,
}

#[derive(Debug, Default)]
pub(crate) struct TraversalCompletionMap<'gram> {
    map: HashMap<TermCompletionKey<'gram>, Vec<TraversalId>>,
}

impl<'gram> TraversalCompletionMap<'gram> {
    pub fn get(
        &'_ self,
        complete_traversal: &Traversal<'gram>,
    ) -> impl Iterator<Item = TraversalId> + '_ {
        let key = TermCompletionKey::new(
            complete_traversal.matching.lhs,
            complete_traversal.input_range.offset.start,
        );
        self.map.get(&key).into_iter().flatten().cloned()
    }
    pub fn insert(&mut self, traversal: &Traversal<'gram>, id: TraversalId) -> bool {
        match traversal.matching.next() {
            Some(unmatched @ Term::Nonterminal(_)) => {
                let key =
                    TermCompletionKey::new(unmatched, traversal.input_range.offset.total_len());
                self.map.entry(key).or_default().push(id);
                true
            }
            _ => false,
        }
    }
}

/// Key used for "incomplete" [`Traversal`]
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct TermCompletionKey<'gram> {
    input_start: usize,
    matching: &'gram Term,
}

impl<'gram> TermCompletionKey<'gram> {
    pub fn new(matching: &'gram Term, input_start: usize) -> Self {
        Self {
            matching,
            input_start,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct TraversalQueue<'gram> {
    arena: AppendOnlyVec<Traversal<'gram>, TraversalId>,
    queue: VecDeque<TraversalId>,
    incomplete: TraversalCompletionMap<'gram>,
    processed: HashSet<TraversalDuplicateKey>,
}

impl<'gram> TraversalQueue<'gram> {
    pub fn new(
        grammar: &GrammarMatching<'gram>,
        input_range: InputRange<'gram>,
        starting_term: &'gram Term,
    ) -> Self {
        let queue = VecDeque::new();
        let starting_traversals = grammar
            .get_productions_by_lhs(starting_term)
            .map(|prod| Traversal::start_production(prod, &input_range));

        let mut traversal_queue = Self {
            queue,
            ..Default::default()
        };

        traversal_queue.extend(starting_traversals);

        traversal_queue
    }

    /// Extend queue with new [`Traversal`]s. Ignores duplicates, according to [`TraversalDuplicateKey`]
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

            let traversal = self.arena.get(id).unwrap();
            self.incomplete.insert(traversal, id);
        }
    }

    /// Pop the next [`Traversal`] from the queue, and invoke a provided "handler" function.
    /// Any newly created [`Traversal`] by the "handler" should be placed in the provided output buffer,
    /// which will be added to the queue (and filtered for duplicates).
    pub fn handle_pop<H>(&mut self, mut handler: H) -> Option<Rc<ProductionMatch<'gram>>>
    where
        H: FnMut(
            TraversalId,
            &AppendOnlyVec<Traversal<'gram>, TraversalId>,
            &mut TraversalCompletionMap<'gram>,
            &mut Vec<Traversal<'gram>>,
        ) -> Option<Rc<ProductionMatch<'gram>>>,
    {
        let _span = tracing::span!(tracing::Level::TRACE, "Queue::handle_pop").entered();
        let mut created = Vec::<Traversal>::new();

        while let Some(id) = self.queue.pop_front() {
            let prod_match = handler(id, &self.arena, &mut self.incomplete, &mut created);
            self.extend(created.drain(..));

            if prod_match.is_some() {
                return prod_match;
            }
        }

        None
    }
}
