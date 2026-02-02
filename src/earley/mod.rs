mod input_range;
mod traversal;

use crate::parser::grammar::ParseGrammar;
use crate::{GrammarParser, ParseTree, ParseTreeNode, Term, tracing};
use input_range::InputRange;
use std::collections::{HashSet, VecDeque};
use std::rc::Rc;
use traversal::{TermMatch, Traversal, TraversalId, TraversalTree};

pub fn parse<'gram>(
    grammar: &'gram GrammarParser<'gram>,
    input: &'gram str,
    starting_term: Option<&'gram Term>,
) -> impl Iterator<Item = ParseTree<'gram>> {
    let _span = tracing::span!(DEBUG, "earley::parse").entered();
    ParseTreeIter::new(ParserHold::Borrowed(grammar), input, starting_term)
}

/// Parse using an owned parser (e.g. from deprecated `Grammar::parse_input`).
/// The iterator holds `Rc<GrammarParser>` to keep the parser alive.
pub fn parse_with_parser_rc<'gram>(
    parser: Rc<GrammarParser<'gram>>,
    input: &'gram str,
    starting_term: Option<&'gram Term>,
) -> impl Iterator<Item = ParseTree<'gram>> {
    let _span = tracing::span!(DEBUG, "earley::parse_with_parser_rc").entered();
    ParseTreeIter::new(ParserHold::Owned(parser), input, starting_term)
}

/// Holds either a borrowed or owned parser so the iterator can keep it alive when needed.
///
/// Only required for the deprecated `Grammar::parse_input` and `Grammar::parse_input_starting_with` methods.
/// Prefer `GrammarParser::parse_input` and `GrammarParser::parse_input_starting_with` instead.
#[derive(Debug)]
enum ParserHold<'gram> {
    Borrowed(&'gram GrammarParser<'gram>),
    Owned(Rc<GrammarParser<'gram>>),
}

impl<'gram> ParserHold<'gram> {
    fn as_ref(&self) -> &GrammarParser<'gram> {
        match self {
            ParserHold::Borrowed(p) => p,
            ParserHold::Owned(rc) => rc.as_ref(),
        }
    }
}

/// A queue of [`TraversalId`] for processing, with repetitions ignored.
#[derive(Debug, Default)]
struct TraversalQueue {
    processed: HashSet<TraversalId>,
    queue: VecDeque<TraversalId>,
}

impl TraversalQueue {
    pub fn pop_front(&mut self) -> Option<TraversalId> {
        self.queue.pop_front()
    }
    pub fn push_back(&mut self, id: TraversalId) {
        if self.processed.insert(id) {
            self.queue.push_back(id);
        }
    }
    /// Add starting traversals to back of queue
    pub fn push_back_starting<'gram>(
        &mut self,
        traversal_tree: &mut TraversalTree<'gram>,
        grammar: &ParseGrammar<'gram>,
        starting_term: &'gram Term,
        input: &InputRange<'gram>,
    ) {
        for starting_prod in grammar.get_productions_by_lhs(starting_term) {
            let traversal = traversal_tree.predict_starting(starting_prod, input);
            self.push_back(traversal);
        }
    }
}

/// Create a [`ParseTree`] starting at the root [`TraversalId`].
fn parse_tree<'gram>(
    traversal_tree: &TraversalTree<'gram>,
    grammar: &Rc<ParseGrammar<'gram>>,
    traversal_id: TraversalId,
) -> ParseTree<'gram> {
    let production = {
        let traversal = traversal_tree.get(traversal_id);
        grammar.get_production_by_id(traversal.production_id)
    };
    let mut rhs = Vec::with_capacity(production.rhs.terms.len());
    for term_match in traversal_tree.get_matched(traversal_id) {
        rhs.push(match term_match {
            TermMatch::Terminal(term) => ParseTreeNode::Terminal(term),
            TermMatch::Nonterminal(traversal_id) => {
                ParseTreeNode::Nonterminal(parse_tree(traversal_tree, grammar, *traversal_id))
            }
        });
    }

    ParseTree::new(production.lhs, rhs)
}

/// Pops [Traversal] from the provided queue, and follows
/// the core [Earley parsing](https://en.wikipedia.org/wiki/Earley_parser) algorithm.
fn earley<'gram>(
    queue: &mut TraversalQueue,
    traversal_tree: &mut TraversalTree<'gram>,
    completions: &mut CompletionMap<'gram>,
    grammar: &Rc<ParseGrammar<'gram>>,
) -> Option<TraversalId> {
    let _span = tracing::span!(DEBUG, "earley").entered();
    while let Some(traversal_id) = queue.pop_front() {
        tracing::event!(
            TRACE,
            "earley queue pop: {:#?}",
            traversal_tree.get(traversal_id)
        );
        let traversal = traversal_tree.get(traversal_id);

        match traversal_tree.get_matching(traversal_id) {
            Some(nonterminal @ Term::Nonterminal(_)) => {
                let _span = tracing::span!(DEBUG, "Predict").entered();

                let lhs = grammar.get_production_by_id(traversal.production_id).lhs;

                completions.insert(traversal, lhs);

                let input_range = traversal.input_range;

                for production in grammar.get_productions_by_lhs(nonterminal) {
                    let predicted = traversal_tree.predict(production, &input_range);
                    tracing::event!(TRACE, "predicted: {predicted:#?}");
                    queue.push_back(predicted);
                }

                for completed in completions.get_complete(nonterminal, &input_range) {
                    let term_match = TermMatch::Nonterminal(completed);
                    let prior_completed = traversal_tree.match_term(traversal_id, term_match);
                    tracing::event!(TRACE, "prior_completed: {prior_completed:#?}");
                    queue.push_back(prior_completed);
                }
            }
            Some(Term::Terminal(term)) => {
                let _span = tracing::span!(DEBUG, "Scan").entered();
                if traversal.input_range.next().starts_with(term) {
                    let term_match = TermMatch::Terminal(term);
                    let scanned = traversal_tree.match_term(traversal_id, term_match);
                    tracing::event!(TRACE, "scanned: {scanned:#?}");
                    queue.push_back(scanned);
                }
            }
            None => {
                let _span = tracing::span!(DEBUG, "Complete").entered();

                let is_full_traversal =
                    traversal.is_starting && traversal.input_range.is_complete();
                let lhs = grammar.get_production_by_id(traversal.production_id).lhs;

                completions.insert(traversal, lhs);

                for incomplete_traversal_id in completions.get_incomplete(lhs, traversal) {
                    let term_match = TermMatch::Nonterminal(traversal_id);
                    let completed = traversal_tree.match_term(incomplete_traversal_id, term_match);

                    tracing::event!(TRACE, "completed: {completed:#?}");
                    queue.push_back(completed);
                }

                if is_full_traversal {
                    return Some(traversal_id);
                }
            }
        }
    }

    None
}

#[derive(Debug)]
struct ParseTreeIter<'gram> {
    parser: ParserHold<'gram>,
    traversal_tree: TraversalTree<'gram>,
    queue: TraversalQueue,
    completions: CompletionMap<'gram>,
}

impl<'gram> ParseTreeIter<'gram> {
    pub fn new(
        parser: ParserHold<'gram>,
        input: &'gram str,
        starting_term: Option<&'gram Term>,
    ) -> Self {
        let _span = tracing::span!(DEBUG, "ParseTreeIter::new").entered();
        let input_range = InputRange::new(input);
        let mut traversal_tree = TraversalTree::default();
        let mut queue = TraversalQueue::default();
        let completions = CompletionMap::with_capacity(32, 32);
        let parser_ref = parser.as_ref();
        let starting_term = starting_term.unwrap_or(parser_ref.starting_term);

        queue.push_back_starting(
            &mut traversal_tree,
            parser_ref.parse_grammar.as_ref(),
            starting_term,
            &input_range,
        );

        Self {
            traversal_tree,
            parser,
            queue,
            completions,
        }
    }
}

impl<'gram> Iterator for ParseTreeIter<'gram> {
    type Item = ParseTree<'gram>;
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            queue,
            completions,
            parser,
            traversal_tree,
        } = self;
        let parse_grammar = &parser.as_ref().parse_grammar;

        earley(queue, traversal_tree, completions, parse_grammar).map(|traversal_id| {
            let _span = tracing::span!(DEBUG, "next_parse_tree").entered();
            let parse_tree = parse_tree(traversal_tree, parse_grammar, traversal_id);
            tracing::event!(TRACE, "\n{parse_tree}");
            parse_tree
        })
    }
}
/// Key used for "incomplete" [`Traversal`] in [`CompletionMap`]
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct CompletionKey<'gram> {
    term: &'gram Term,
    input_start: usize,
}

impl<'gram> CompletionKey<'gram> {
    pub const fn new_start(term: &'gram Term, input: &InputRange<'gram>) -> Self {
        Self {
            term,
            input_start: input.offset.start,
        }
    }
    pub const fn new_total(term: &'gram Term, input: &InputRange<'gram>) -> Self {
        Self {
            term,
            input_start: input.offset.total_len(),
        }
    }
}

/// Insert into a sorted Vec; no-op if already present. Keeps iteration order stable (same as `BTreeSet`).
fn sorted_vec_insert(vec: &mut Vec<TraversalId>, id: TraversalId) {
    match vec.binary_search(&id) {
        Ok(_) => {}
        Err(i) => vec.insert(i, id),
    }
}

#[derive(Debug)]
pub(crate) struct CompletionMap<'gram> {
    incomplete: crate::HashMap<CompletionKey<'gram>, Vec<TraversalId>>,
    complete: crate::HashMap<CompletionKey<'gram>, Vec<TraversalId>>,
}

impl<'gram> Default for CompletionMap<'gram> {
    fn default() -> Self {
        Self::with_capacity(0, 0)
    }
}

impl<'gram> CompletionMap<'gram> {
    /// Create with reserved capacity to reduce rehashing during parsing.
    pub fn with_capacity(incomplete: usize, complete: usize) -> Self {
        Self {
            incomplete: crate::HashMap::with_capacity(incomplete),
            complete: crate::HashMap::with_capacity(complete),
        }
    }
    pub fn get_incomplete<'map>(
        &'map self,
        term: &'gram Term,
        complete_traversal: &Traversal<'gram>,
    ) -> impl Iterator<Item = TraversalId> + use<'map> {
        let _span = tracing::span!(DEBUG, "get_incomplete").entered();
        let key = CompletionKey::new_start(term, &complete_traversal.input_range);
        self.incomplete.get(&key).into_iter().flatten().cloned()
    }
    pub fn get_complete<'map>(
        &'map self,
        term: &'gram Term,
        input_range: &InputRange<'gram>,
    ) -> impl Iterator<Item = TraversalId> + use<'map> {
        let _span = tracing::span!(DEBUG, "get_complete").entered();
        let key = CompletionKey::new_total(term, input_range);
        self.complete.get(&key).into_iter().flatten().cloned()
    }
    pub fn insert(&mut self, traversal: &Traversal<'gram>, lhs: &'gram Term) {
        let _span = tracing::span!(DEBUG, "insert").entered();
        match traversal.next_unmatched() {
            Some(Term::Terminal(_)) => {
                // do nothing, because terminals are irrelevant to completion
            }
            Some(unmatched @ Term::Nonterminal(_)) => {
                let key = CompletionKey::new_total(unmatched, &traversal.input_range);
                sorted_vec_insert(self.incomplete.entry(key).or_default(), traversal.id);
            }
            None => {
                let key = CompletionKey::new_start(lhs, &traversal.input_range);
                sorted_vec_insert(self.complete.entry(key).or_default(), traversal.id);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    #[derive(Debug, Clone)]
    struct NestedEmptyGrammar(Grammar);
    impl Arbitrary for NestedEmptyGrammar {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut grammar: Grammar = "
            <start> ::= <a> <empty>
            <a> ::= 'a' <empty>"
                .parse()
                .unwrap();

            let mut expressions: Vec<_> = grammar
                .productions_iter_mut()
                .flat_map(|prod| prod.rhs_iter_mut())
                .collect();

            let expr_indexes: Vec<usize> = (0..expressions.len()).collect();
            let expr_choice_index = g.choose(&expr_indexes).unwrap();
            let expr_choice: &mut crate::Expression =
                expressions.get_mut(*expr_choice_index).unwrap();

            let term_choice_indexes: Vec<usize> = (0..expr_choice.terms.len()).collect();
            let term_choice_index = g.choose(&term_choice_indexes).unwrap();

            expr_choice
                .terms
                .insert(*term_choice_index, Term::Nonterminal(String::from("empty")));

            grammar.add_production("<empty> ::= ''".parse().unwrap());

            Self(grammar)
        }
    }

    fn prop_empty_rules_allow_parse(grammar: NestedEmptyGrammar) -> TestResult {
        let input = "a";
        let parser = GrammarParser::new(&grammar.0).unwrap();

        let mut parses = parse(&parser, input, None);
        TestResult::from_bool(parses.next().is_some())
    }

    #[test]
    fn empty_rules_allow_parse() {
        QuickCheck::new()
            .tests(1000)
            .quickcheck(prop_empty_rules_allow_parse as fn(NestedEmptyGrammar) -> TestResult)
    }
}
