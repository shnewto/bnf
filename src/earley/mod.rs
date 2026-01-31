//! Earley parser implementation.
//!
//! Lifetimes: `'parser` = borrow lifetime (grammar, input, starting term); `'gram` = grammar data lifetime.

mod input_range;
mod traversal;

use crate::parser::grammar::ParseGrammar;
use crate::{ParseTree, ParseTreeNode, Term, tracing};
use input_range::InputRange;
use std::collections::{BTreeSet, HashSet, VecDeque};
use std::rc::Rc;
use traversal::{TermMatch, TraversalId, TraversalTree};

/// Low-level parse entry point; callers should prefer [`crate::GrammarParser::parse_input`].
/// Kept public for external use when a pre-built `Grammar` is already available.
#[allow(dead_code)]
pub fn parse<'parser, 'gram>(
    grammar: &'parser crate::grammar::Grammar<'gram>,
    input: &'parser str,
) -> impl Iterator<Item = ParseTree<'parser, 'gram>>
where
    'gram: 'parser,
{
    ParseTreeIter::new(grammar, input)
}

/// Low-level parse entry point; callers should prefer [`crate::GrammarParser::parse_input_starting_with`].
/// Kept public for external use when a pre-built `Grammar` and starting term are already available.
#[allow(dead_code)]
pub fn parse_starting_with<'parser, 'gram>(
    grammar: &'parser crate::grammar::Grammar<'gram>,
    input: &'parser str,
    starting_term: &'parser Term<'gram>,
) -> impl Iterator<Item = ParseTree<'parser, 'gram>>
where
    'gram: 'parser,
{
    ParseTreeIter::new_starting_with(grammar, input, starting_term)
}

/// Parse input using a pre-built `ParseGrammar`, starting with the given term.
/// This allows reusing the `ParseGrammar` for multiple inputs.
pub(crate) fn parse_starting_with_grammar<'parser, 'gram>(
    parse_grammar: &Rc<ParseGrammar<'parser, 'gram>>,
    input: &'parser str,
    starting_term: &'parser Term<'gram>,
) -> impl Iterator<Item = ParseTree<'parser, 'gram>> {
    // Clone the Rc (just increments reference count, no data copying)
    ParseTreeIter::new_starting_with_grammar(Rc::clone(parse_grammar), input, starting_term)
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
    pub fn push_back_starting<'parser, 'gram>(
        &mut self,
        traversal_tree: &mut TraversalTree<'parser, 'gram>,
        grammar: &ParseGrammar<'parser, 'gram>,
        starting_term: &'parser Term<'gram>,
        input: &InputRange<'parser>,
    ) {
        for starting_prod in grammar.get_productions_by_lhs(starting_term) {
            let traversal = traversal_tree.predict_starting(starting_prod, input);
            self.push_back(traversal);
        }
    }
}

/// Create a [`ParseTree`] starting at the root [`TraversalId`].
fn parse_tree<'parser, 'gram>(
    traversal_tree: &TraversalTree<'parser, 'gram>,
    grammar: &Rc<ParseGrammar<'parser, 'gram>>,
    traversal_id: TraversalId,
) -> ParseTree<'parser, 'gram> {
    let production = {
        let traversal = traversal_tree.get(traversal_id);
        grammar.get_production_by_id(traversal.production_id)
    };
    let rhs = traversal_tree
        .get_matched(traversal_id)
        .map(|term_match| match term_match {
            TermMatch::Terminal(term) => ParseTreeNode::Terminal(term),
            TermMatch::Nonterminal(traversal_id) => {
                ParseTreeNode::Nonterminal(parse_tree(traversal_tree, grammar, *traversal_id))
            }
        })
        .collect::<Vec<ParseTreeNode>>();

    ParseTree::new(production.lhs, rhs)
}

/// Pops [Traversal] from the provided queue, and follows
/// the core [Earley parsing](https://en.wikipedia.org/wiki/Earley_parser) algorithm.
fn earley<'parser, 'gram>(
    queue: &mut TraversalQueue,
    traversal_tree: &mut TraversalTree<'parser, 'gram>,
    completions: &mut CompletionMap<'gram>,
    grammar: &Rc<ParseGrammar<'parser, 'gram>>,
) -> Option<TraversalId> {
    let _span = tracing::span!(tracing::Level::DEBUG, "earley").entered();
    while let Some(traversal_id) = queue.pop_front() {
        tracing::event!(
            tracing::Level::TRACE,
            "earley queue pop: {:#?}",
            traversal_tree.get(traversal_id)
        );
        let traversal = traversal_tree.get(traversal_id);

        let next_unmatched_ref = traversal_tree.get_matching(traversal_id);
        // Terminal string for scanning the input (Scan step).
        let next_terminal_str: Option<&'parser str> = next_unmatched_ref.and_then(|t| match t {
            Term::Terminal(s) => Some(s.as_ref()),
            _ => None,
        });
        // Next term ref for completion map and LHS lookups (Predict/Complete).
        let next_term_ref = next_unmatched_ref.and_then(|t| grammar.get_term_ref(t));
        let next_unmatched = next_unmatched_ref.cloned();

        match next_unmatched {
            Some(ref _nonterminal @ Term::Nonterminal(_)) => {
                let _span = tracing::span!(tracing::Level::DEBUG, "Predict").entered();

                let lhs = grammar.get_production_by_id(traversal.production_id).lhs;

                completions.insert(traversal_id, next_term_ref, &traversal.input_range, lhs);

                if let Some(term_ref) = next_term_ref {
                    let input_range = traversal.input_range.clone();
                    let productions: Vec<_> = grammar.get_productions_by_lhs(term_ref).collect();
                    let completed_ids: Vec<_> =
                        completions.get_complete(term_ref, &input_range).collect();

                    for production in productions {
                        let predicted = traversal_tree.predict(production, &input_range);
                        tracing::event!(tracing::Level::TRACE, "predicted: {predicted:#?}");
                        queue.push_back(predicted);
                    }

                    for completed in completed_ids {
                        let term_match = TermMatch::Nonterminal(completed);
                        let prior_completed = traversal_tree.match_term(traversal_id, term_match);
                        tracing::event!(
                            tracing::Level::TRACE,
                            "prior_completed: {prior_completed:#?}"
                        );
                        queue.push_back(prior_completed);
                    }
                }
                // undefined nonterminal: no productions to predict, no completions to match
            }
            Some(Term::Terminal(_)) => {
                let _span = tracing::span!(tracing::Level::DEBUG, "Scan").entered();
                if let Some(term_str) = next_terminal_str
                    && traversal.input_range.next().starts_with(term_str)
                {
                    let term_match = TermMatch::Terminal(term_str);
                    let scanned = traversal_tree.match_term(traversal_id, term_match);
                    tracing::event!(tracing::Level::TRACE, "scanned: {scanned:#?}");
                    queue.push_back(scanned);
                }
            }
            Some(ref _anon @ Term::AnonymousNonterminal(_)) => {
                let _span = tracing::span!(tracing::Level::DEBUG, "Predict_anon").entered();

                let lhs = grammar.get_production_by_id(traversal.production_id).lhs;

                completions.insert(traversal_id, next_term_ref, &traversal.input_range, lhs);

                if let Some(term_ref) = next_term_ref {
                    let input_range = traversal.input_range.clone();
                    let productions: Vec<_> = grammar.get_productions_by_lhs(term_ref).collect();
                    let completed_ids: Vec<_> =
                        completions.get_complete(term_ref, &input_range).collect();

                    for production in productions {
                        let predicted = traversal_tree.predict(production, &input_range);
                        tracing::event!(tracing::Level::TRACE, "predicted: {predicted:#?}");
                        queue.push_back(predicted);
                    }

                    for completed in completed_ids {
                        let term_match = TermMatch::Nonterminal(completed);
                        let prior_completed = traversal_tree.match_term(traversal_id, term_match);
                        tracing::event!(
                            tracing::Level::TRACE,
                            "prior_completed: {prior_completed:#?}"
                        );
                        queue.push_back(prior_completed);
                    }
                }
            }
            None => {
                let _span = tracing::span!(tracing::Level::DEBUG, "Complete").entered();

                let is_full_traversal =
                    traversal.is_starting && traversal.input_range.is_complete();
                let lhs = grammar.get_production_by_id(traversal.production_id).lhs;

                completions.insert(traversal_id, next_term_ref, &traversal.input_range, lhs);

                for incomplete_traversal_id in
                    completions.get_incomplete(lhs, &traversal.input_range)
                {
                    let term_match = TermMatch::Nonterminal(traversal_id);
                    let completed = traversal_tree.match_term(incomplete_traversal_id, term_match);

                    tracing::event!(tracing::Level::TRACE, "completed: {completed:#?}");
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
struct ParseTreeIter<'parser, 'gram> {
    traversal_tree: TraversalTree<'parser, 'gram>,
    grammar: Rc<ParseGrammar<'parser, 'gram>>,
    queue: TraversalQueue,
    completions: CompletionMap<'gram>,
}

impl<'parser, 'gram> ParseTreeIter<'parser, 'gram> {
    /// Low-level constructor; prefer [`crate::GrammarParser::parse_input`].
    #[allow(dead_code)]
    pub fn new(grammar: &'parser crate::grammar::Grammar<'gram>, input: &'parser str) -> Self
    where
        'gram: 'parser,
    {
        let starting_term = grammar
            .starting_term()
            .expect("Grammar must have one production to parse");

        Self::new_starting_with(grammar, input, starting_term)
    }

    /// Low-level constructor; prefer [`crate::GrammarParser::parse_input_starting_with`].
    #[allow(dead_code)]
    pub fn new_starting_with(
        grammar: &'parser crate::grammar::Grammar<'gram>,
        input: &'parser str,
        starting_term: &'parser Term<'gram>,
    ) -> Self
    where
        'gram: 'parser,
    {
        let parse_grammar = Rc::new(ParseGrammar::new(grammar));
        Self::new_starting_with_grammar(parse_grammar, input, starting_term)
    }

    pub(crate) fn new_starting_with_grammar(
        parse_grammar: Rc<ParseGrammar<'parser, 'gram>>,
        input: &'parser str,
        starting_term: &'parser Term<'gram>,
    ) -> Self {
        let input = InputRange::new(input);
        let mut traversal_tree = TraversalTree::default();
        let mut queue = TraversalQueue::default();
        let completions = CompletionMap::default();

        queue.push_back_starting(&mut traversal_tree, &parse_grammar, starting_term, &input);

        Self {
            traversal_tree,
            grammar: parse_grammar,
            queue,
            completions,
        }
    }
}

impl<'parser, 'gram> Iterator for ParseTreeIter<'parser, 'gram> {
    type Item = ParseTree<'parser, 'gram>;
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            queue,
            completions,
            grammar,
            traversal_tree,
        } = self;

        earley(queue, traversal_tree, completions, grammar).map(|traversal_id| {
            let _span = tracing::span!(tracing::Level::DEBUG, "next_parse_tree").entered();
            let parse_tree = parse_tree(traversal_tree, grammar, traversal_id);
            tracing::event!(tracing::Level::TRACE, "\n{parse_tree}");
            parse_tree
        })
    }
}
/// Key for the completion map; stores an owned `Term` so we can use it as a `HashMap` key under the two-lifetime setup.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompletionKey<'gram> {
    term: Term<'gram>,
    input_start: usize,
}

impl<'gram> CompletionKey<'gram> {
    pub fn new_start(term: &Term<'gram>, input: &InputRange<'_>) -> Self {
        Self {
            term: term.clone(),
            input_start: input.offset.start,
        }
    }
    pub fn new_total(term: &Term<'gram>, input: &InputRange<'_>) -> Self {
        Self {
            term: term.clone(),
            input_start: input.offset.total_len(),
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct CompletionMap<'gram> {
    incomplete: crate::HashMap<CompletionKey<'gram>, BTreeSet<TraversalId>>,
    complete: crate::HashMap<CompletionKey<'gram>, BTreeSet<TraversalId>>,
}

impl<'parser, 'gram> CompletionMap<'gram> {
    pub fn get_incomplete<'map>(
        &'map self,
        term: &'parser Term<'gram>,
        input_range: &InputRange<'parser>,
    ) -> impl Iterator<Item = TraversalId> + use<'map> {
        let _span = tracing::span!(tracing::Level::DEBUG, "get_incomplete").entered();
        let key = CompletionKey::new_start(term, input_range);
        self.incomplete.get(&key).into_iter().flatten().cloned()
    }
    pub fn get_complete<'map>(
        &'map self,
        term: &'parser Term<'gram>,
        input_range: &InputRange<'parser>,
    ) -> impl Iterator<Item = TraversalId> + use<'map> {
        let _span = tracing::span!(tracing::Level::DEBUG, "get_complete").entered();
        let key = CompletionKey::new_total(term, input_range);
        self.complete.get(&key).into_iter().flatten().cloned()
    }
    pub fn insert(
        &mut self,
        traversal_id: TraversalId,
        next_unmatched: Option<&'parser Term<'gram>>,
        input_range: &InputRange<'parser>,
        lhs: &'parser Term<'gram>,
    ) {
        let _span = tracing::span!(tracing::Level::DEBUG, "insert").entered();
        match next_unmatched {
            Some(Term::Terminal(_)) => {} // Terminals are irrelevant to completion (no LHS lookups).
            Some(unmatched) => {
                let key = CompletionKey::new_total(unmatched, input_range);
                self.incomplete.entry(key).or_default().insert(traversal_id);
            }
            None => {
                let key = CompletionKey::new_start(lhs, input_range);
                self.complete.entry(key).or_default().insert(traversal_id);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
    use std::borrow::Cow;

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
            let expr_choice: &mut crate::Expression<'static> =
                expressions.get_mut(*expr_choice_index).unwrap();

            let term_choice_indexes: Vec<usize> = (0..expr_choice.terms.len()).collect();
            let term_choice_index = g.choose(&term_choice_indexes).unwrap();

            expr_choice.terms.to_mut().insert(
                *term_choice_index,
                Term::Nonterminal(Cow::Owned(String::from("empty"))),
            );

            grammar.add_production("<empty> ::= ''".parse().unwrap());

            Self(grammar)
        }
    }

    fn prop_empty_rules_allow_parse(grammar: NestedEmptyGrammar) -> TestResult {
        let input = "a";
        let grammar = grammar.0;

        let mut parses = parse(&grammar, input);
        TestResult::from_bool(parses.next().is_some())
    }

    #[test]
    fn empty_rules_allow_parse() {
        QuickCheck::new()
            .tests(1000)
            .quickcheck(prop_empty_rules_allow_parse as fn(NestedEmptyGrammar) -> TestResult)
    }
}
