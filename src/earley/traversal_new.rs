use super::{grammar::ProductionId, GrammarMatching, InputRange, Production};
use crate::{
    append_vec::{append_only_vec_id, AppendOnlyVec},
    tracing, Grammar, Term,
};
use std::collections::HashMap;
use std::rc::Rc;

/// A [`crate::Term`] which has been "matched" while parsing input
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TermMatch<'gram> {
    /// [`crate::Term::Terminal`] which matched with a string literal
    Terminal(&'gram str),
    /// [`crate::Term::Nonterminal`] which was matched with a fully completed traversal
    Nonterminal(TraversalId),
}

append_only_vec_id!(pub(crate) TraversalId);

#[derive(Debug)]
pub(crate) struct Traversal<'gram> {
    pub id: TraversalId,
    pub unmatched: &'gram [crate::Term],
    pub input_range: InputRange<'gram>,
    pub production_id: ProductionId,
    from: Option<TraversalEdge<'gram>>,
}

impl<'gram> Traversal<'gram> {
    pub fn next_unmatched(&self) -> Option<&'gram Term> {
        self.unmatched.get(0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TraversalEdge<'gram> {
    pub term: TermMatch<'gram>,
    pub parent_id: TraversalId,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TraversalRootKey {
    production_id: super::grammar::ProductionId,
    input_start: usize,
}

type TraversalArena<'gram> = AppendOnlyVec<Traversal<'gram>, TraversalId>;
type TreeRootMap = HashMap<TraversalRootKey, TraversalId>;
type TreeEdgeMap<'gram> = HashMap<TraversalEdge<'gram>, TraversalId>;

#[derive(Debug)]
pub(crate) struct TraversalMatchIter<'gram, 'tree> {
    tree: &'tree TraversalTree<'gram>,
    current: TraversalId,
    last: TraversalId,
}

impl<'gram, 'tree> TraversalMatchIter<'gram, 'tree> {
    pub fn new(last: TraversalId, tree: &'tree TraversalTree<'gram>) -> Self {
        let mut current = last;
        while let Some(edge) = &tree.get(current).from {
            current = edge.parent_id;
        }

        Self {
            current,
            tree,
            last,
        }
    }
}

impl<'gram, 'tree> Iterator for TraversalMatchIter<'gram, 'tree> {
    type Item = &'tree TermMatch<'gram>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.current == self.last {
            return None;
        }

        let mut scan = self.last;
        while let Some(edge) = &self.tree.get(scan).from {
            if self.current == edge.parent_id {
                self.current = scan;
                return Some(&edge.term);
            }

            scan = edge.parent_id;
        }

        None
    }
}

#[derive(Debug, Default)]
pub(crate) struct TraversalTree<'gram> {
    arena: TraversalArena<'gram>,
    tree_roots: TreeRootMap,
    edges: TreeEdgeMap<'gram>,
}

impl<'gram> TraversalTree<'gram> {
    pub fn get(&self, id: TraversalId) -> &Traversal<'gram> {
        self.arena.get(id).expect("valid traversal ID")
    }
    pub fn get_matching(&self, id: TraversalId) -> Option<&'gram Term> {
        self.get(id).next_unmatched()
    }
    pub fn get_matched(&self, id: TraversalId) -> impl Iterator<Item = &TermMatch<'gram>> {
        TraversalMatchIter::new(id, self)
    }
    pub fn predict(
        &mut self,
        production: &Production<'gram>,
        input_range: &InputRange<'gram>,
    ) -> &Traversal {
        fn inner<'gram>(
            arena: &mut TraversalArena<'gram>,
            tree_roots: &mut TreeRootMap,
            input_range: &InputRange<'gram>,
            production: &Production<'gram>,
        ) -> TraversalId {
            let production_id = production.id;
            let traversal_root_key = TraversalRootKey {
                production_id,
                input_start: input_range.offset.total_len(),
            };

            let traversal_root = tree_roots.entry(traversal_root_key).or_insert_with(|| {
                let traversal = arena.push_with_id(|id| Traversal {
                    id,
                    production_id,
                    unmatched: &production.rhs.terms,
                    input_range: input_range.after(),
                    from: None,
                });
                traversal.id
            });

            *traversal_root
        }

        let predicted_id = inner(
            &mut self.arena,
            &mut self.tree_roots,
            input_range,
            production,
        );

        self.get(predicted_id)
    }
    pub fn match_term(&mut self, parent: TraversalId, term: TermMatch<'gram>) -> &Traversal {
        fn inner<'gram>(
            arena: &mut TraversalArena<'gram>,
            edges: &mut TreeEdgeMap<'gram>,
            parent: TraversalId,
            term: TermMatch<'gram>,
        ) -> TraversalId {
            let parent = arena.get(parent).expect("valid parent traversal ID");
            let input_range = match term {
                TermMatch::Terminal(term) => parent.input_range.advance_by(term.len()),
                TermMatch::Nonterminal(nonterminal_traversal_id) => {
                    let nonterminal_traversal = arena
                        .get(nonterminal_traversal_id)
                        .expect("valid completed traversal ID");

                    parent
                        .input_range
                        .advance_by(nonterminal_traversal.input_range.offset.len)
                }
            };

            let parent_id = parent.id;
            let production_id = parent.production_id;
            let unmatched = &parent.unmatched[1..];
            let from = TraversalEdge { term, parent_id };

            let matched = edges.entry(from).or_insert_with_key(|from| {
                let traversal = arena.push_with_id(|id| Traversal {
                    id,
                    production_id,
                    unmatched,
                    input_range: input_range.clone(),
                    from: Some(from.clone()),
                });
                traversal.id
            });

            *matched
        }

        let matched_id = inner(&mut self.arena, &mut self.edges, parent, term);

        self.get(matched_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dna_grammar() -> Grammar {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
            <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        grammar
    }

    fn traversal_test_setup<'a>(
        grammar: &'a Grammar,
        input: &'static str,
    ) -> (GrammarMatching<'a>, InputRange<'static>, TraversalTree<'a>) {
        let matching = GrammarMatching::new(&grammar);
        let input = InputRange::new(input);
        let tree = TraversalTree::default();

        (matching, input, tree)
    }

    #[test]
    fn predict() {
        let grammar = dna_grammar();
        let (grammar, input, mut tree) = traversal_test_setup(&grammar, "GATTACA");
        let production = grammar.productions_iter().next().unwrap();

        let predicted = tree.predict(production, &input);

        assert_eq!(&production.rhs.terms, predicted.unmatched);
    }

    #[test]
    fn predict_again() {
        let grammar = dna_grammar();
        let (grammar, input, mut tree) = traversal_test_setup(&grammar, "GATTACA");
        let production = grammar.productions_iter().next().unwrap();

        let first = tree.predict(production, &input).id;
        let again = tree.predict(production, &input).id;

        assert_eq!(first, again);
    }

    #[test]
    fn match_term() {
        let grammar = "<start> ::= 'A'".parse().unwrap();
        let (grammar, input, mut tree) = traversal_test_setup(&grammar, "AAAA");
        let production = grammar.productions_iter().next().unwrap();
        let prediction = tree.predict(production, &input).id;
        let term_match = TermMatch::Terminal("A");

        let scanned = tree.match_term(prediction, term_match);

        assert_eq!(scanned.unmatched, &production.rhs.terms[1..]);
    }

    #[test]
    fn match_term_again() {
        let grammar = "<start> ::= 'A'".parse().unwrap();
        let (grammar, input, mut tree) = traversal_test_setup(&grammar, "AAAA");
        let production = grammar.productions_iter().next().unwrap();
        let prediction = tree.predict(production, &input).id;

        let term_match = TermMatch::Terminal("A");

        let first = tree.match_term(prediction, term_match.clone()).id;
        let again = tree.match_term(prediction, term_match.clone()).id;

        assert_eq!(first, again);
    }

    #[test]
    fn match_term_complete() {
        let grammar = "<start> ::= 'A' | 'B' | 'C'".parse().unwrap();
        let (grammar, input, mut tree) = traversal_test_setup(&grammar, "ABC");
        let production = grammar.productions_iter().next().unwrap();
        let prediction = tree.predict(production, &input).id;

        // build match tree of <start> -> 'A', <start> -> 'B', <start> -> 'C'
        for term_match in ["A", "B", "C"] {
            let term_match = TermMatch::Terminal(term_match);
            let traversal = tree.match_term(prediction, term_match);
            assert_eq!(traversal.next_unmatched(), None);
        }
    }
}
