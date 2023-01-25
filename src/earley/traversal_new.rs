use super::{GrammarMatching, InputRange, Production};
use crate::{
    append_vec::{append_only_vec_id, AppendOnlyVec},
    tracing, Grammar, Term,
};
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
    id: TraversalId,
    unmatched: &'gram [crate::Term],
    input_range: InputRange<'gram>,
    from: Option<TraversalEdge<'gram>>,
}

impl<'gram> Traversal<'gram> {
    pub fn is_complete(&self) -> bool {
        self.unmatched.is_empty()
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

#[derive(Debug, Default)]
pub(crate) struct TraversalTree<'gram> {
    arena: AppendOnlyVec<Traversal<'gram>, TraversalId>,
    tree_roots: std::collections::HashMap<TraversalRootKey, TraversalId>,
    edges: std::collections::HashMap<TraversalEdge<'gram>, TraversalId>,
}

impl<'gram> TraversalTree<'gram> {
    pub fn predict(
        &mut self,
        production: &Production<'gram>,
        input_range: &InputRange<'gram>,
    ) -> &Traversal {
        let traversal_root_key = TraversalRootKey {
            production_id: production.id,
            input_start: input_range.offset.total_len(),
        };

        let traversal_root = self
            .tree_roots
            .entry(traversal_root_key)
            .or_insert_with(|| {
                let traversal = self.arena.push_with_id(|id| Traversal {
                    id,
                    unmatched: &production.rhs.terms,
                    input_range: input_range.after(),
                    from: None,
                });
                traversal.id
            });

        self.arena
            .get(*traversal_root)
            .expect("traversal exists after insertion")
    }
    pub fn match_term(&mut self, parent: TraversalId, term: TermMatch<'gram>) -> &Traversal {
        let parent = self.arena.get(parent).expect("parent traversal must exist");
        let input_range = match term {
            TermMatch::Terminal(term) => parent.input_range.advance_by(term.len()),
            TermMatch::Nonterminal(_) => parent.input_range.clone(),
        };

        let parent_id = parent.id;
        let unmatched = &parent.unmatched[1..];
        let from = TraversalEdge { term, parent_id };

        let matched = self.edges.entry(from).or_insert_with_key(|from| {
            let traversal = self.arena.push_with_id(|id| Traversal {
                id,
                unmatched,
                input_range: input_range.clone(),
                from: Some(from.clone()),
            });
            traversal.id
        });

        self.arena
            .get(*matched)
            .expect("traversal exists after insertion")
    }
    pub fn traverse(&mut self, grammar: &GrammarMatching<'gram>, id: TraversalId) -> impl Iterator<Item=&Traversal> {
        let traversal = self.arena.get(id).expect("valid traversal ID");
        match traversal.unmatched.iter().next() {
            // predict
            Some(term @ Term::Nonterminal(_)) => {
                todo!()
            },
            // scan
            Some(Term::Terminal(term)) => {
                todo!()
            }
            // complete
            None => {
                todo!()
                
            }
        }
        std::iter::empty()
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
            assert!(traversal.is_complete());
        }
    }
}
