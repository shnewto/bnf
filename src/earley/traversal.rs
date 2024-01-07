use super::{grammar::ProductionId, InputRange, Production};
use crate::{
    append_vec::{append_only_vec_id, AppendOnlyVec},
    tracing, Term,
};

append_only_vec_id!(pub(crate) TraversalId);

/// A [`crate::Term`] which has been "matched" while parsing input
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TermMatch<'gram> {
    /// [`crate::Term::Terminal`] which matched with a string literal
    Terminal(&'gram str),
    /// [`crate::Term::Nonterminal`] which was matched with a fully completed traversal
    Nonterminal(TraversalId),
}

/// A single step in Earley parsing.
/// Also commonly referred to as an Earley "state".
#[derive(Debug)]
pub(crate) struct Traversal<'gram> {
    pub id: TraversalId,
    /// The unmatched "right hand side" [`Term]s
    pub unmatched: &'gram [crate::Term],
    /// The input text available for parsing
    pub input_range: InputRange<'gram>,
    /// Unique ID for the [Production] used to begin this [`Traversal`]
    pub production_id: ProductionId,
    /// Flag indicating that this [`Traversal`] began at the start of parsing,
    /// and if fully completed then qualifies as a successful parse.
    pub is_starting: bool,
    /// Reference to the parent [`Traversal`] which started this one.
    from: Option<TraversalEdge<'gram>>,
}

impl<'gram> Traversal<'gram> {
    pub const fn next_unmatched(&self) -> Option<&'gram Term> {
        self.unmatched.first()
    }
}

/// The edge which connects [`Traversal`]s in a [`TraversalTree`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TraversalEdge<'gram> {
    pub term: TermMatch<'gram>,
    pub parent_id: TraversalId,
}

/// The root in a [`TraversalTree`].
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TraversalRoot {
    production_id: super::grammar::ProductionId,
    input_start: usize,
}

type TraversalArena<'gram> = AppendOnlyVec<Traversal<'gram>, TraversalId>;
type TreeRootMap = crate::HashMap<TraversalRoot, TraversalId>;
type TreeEdgeMap<'gram> = crate::HashMap<TraversalEdge<'gram>, TraversalId>;

/// Iterator of [`TermMatch`] which resulted in the [`Traversal`].
/// Walks a [`TraversalTree`] from [`TraversalRoot`] along [`TraversalEdge`].
///
/// Because [`Traversal`] only know their immediate parent, this iterator walks the [`TraversalTree`]
/// in a silly way. Starting at the leaf, it walks up and up until finding the next desired [`Traversal`].
/// This leads to wasted and repeated walking of [`TraversalEdge`]s. But in practice, this wasted tree
/// walking seems preferable to alternatives.
#[derive(Debug)]
pub(crate) struct TraversalMatchIter<'gram, 'tree> {
    tree: &'tree TraversalTree<'gram>,
    current: TraversalId,
    last: TraversalId,
}

impl<'gram, 'tree> TraversalMatchIter<'gram, 'tree> {
    pub fn new(last: TraversalId, tree: &'tree TraversalTree<'gram>) -> Self {
        let _span = tracing::span!(tracing::Level::DEBUG, "match_iter_new").entered();
        // walk up the tree until the root is found
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
        let _span = tracing::span!(tracing::Level::DEBUG, "match_iter_next").entered();
        if self.current == self.last {
            return None;
        }

        let mut scan = self.last;
        // walk up the tree until the next item is found
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

/// A tree of [`Traversal`], with [`TermMatch`] used for edges.
/// Earley "predictions" start a tree root, and each scan/complete creates child nodes. e.g.
/// ```txt
/// <start> ::= • <a>        (this is the root of the prediction tree)
/// ├── <start> ::= <a=1> •  (this is a child traversal created by matching <a>)
/// └── <start> ::= <a=2> •  (this is a different child traversal created by a different match with <a>)
/// ```
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
    fn predict_is_starting(
        arena: &mut TraversalArena<'gram>,
        tree_roots: &mut TreeRootMap,
        input_range: &InputRange<'gram>,
        production: &Production<'gram>,
        is_starting: bool,
    ) -> TraversalId {
        let _span =
            tracing::span!(tracing::Level::DEBUG, "traversal_tree_predict_is_starting").entered();
        let production_id = production.id;
        let traversal_root_key = TraversalRoot {
            production_id,
            input_start: input_range.offset.total_len(),
        };

        let traversal_root = tree_roots.entry(traversal_root_key).or_insert_with(|| {
            let traversal = arena.push_with_id(|id| Traversal {
                id,
                production_id,
                unmatched: &production.rhs.terms,
                input_range: input_range.after(),
                is_starting,
                from: None,
            });
            traversal.id
        });

        *traversal_root
    }
    /// Same as [`TraversalTree::predict`] but flagging the [`Traversal`] as a parsing starting point
    pub fn predict_starting(
        &mut self,
        production: &Production<'gram>,
        input_range: &InputRange<'gram>,
    ) -> &Traversal {
        let is_starting = true;
        let predicted_id = Self::predict_is_starting(
            &mut self.arena,
            &mut self.tree_roots,
            input_range,
            production,
            is_starting,
        );

        self.get(predicted_id)
    }
    pub fn predict(
        &mut self,
        production: &Production<'gram>,
        input_range: &InputRange<'gram>,
    ) -> &Traversal {
        let is_starting = false;
        let predicted_id = Self::predict_is_starting(
            &mut self.arena,
            &mut self.tree_roots,
            input_range,
            production,
            is_starting,
        );

        self.get(predicted_id)
    }
    pub fn match_term(&mut self, parent: TraversalId, term: TermMatch<'gram>) -> &Traversal {
        let _span = tracing::span!(tracing::Level::DEBUG, "match_term").entered();
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
            let is_starting = parent.is_starting;
            let from = TraversalEdge { term, parent_id };

            let matched = edges.entry(from).or_insert_with_key(|from| {
                let traversal = arena.push_with_id(|id| Traversal {
                    id,
                    production_id,
                    unmatched,
                    input_range: input_range.clone(),
                    is_starting,
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
    use crate::earley::ParseGrammar;
    use crate::Grammar;

    fn dna_grammar() -> Grammar {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
            <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();

        grammar
    }

    fn traversal_test_setup<'a>(
        grammar: &'a Grammar,
        input: &'static str,
    ) -> (ParseGrammar<'a>, InputRange<'static>, TraversalTree<'a>) {
        let matching = ParseGrammar::new(grammar);
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
