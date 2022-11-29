mod grammar;
mod input_range;
mod traversal;

use crate::{tracing, ParseTree, ParseTreeNode, Term};
use grammar::{GrammarMatching, ProductionMatch, TermMatch};
use input_range::InputRange;
use std::collections::HashMap;
use std::rc::Rc;
use traversal::{EarleyStep, Traversal, TraversalId, TraversalQueue};

/// Key used for "incomplete" [`crate::Production`] during [`complete`]
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

type TermCompletionMap<'gram> = HashMap<TermCompletionKey<'gram>, Vec<TraversalId>>;

fn predict<'gram, 'a>(
    traversal: &'a Traversal<'gram>,
    nonterminal: &'gram Term,
    grammar: &'a GrammarMatching<'gram>,
) -> impl Iterator<Item = Traversal<'gram>> + 'a {
    grammar
        .get_productions_by_lhs(nonterminal)
        .map(|prod| Traversal::start_production(prod, &traversal.input_range))
}

fn complete_nullable<'gram, 'a>(
    traversal: &'a Traversal<'gram>,
    nonterminal: &'gram Term,
    grammar: &'a GrammarMatching<'gram>,
) -> impl Iterator<Item = Traversal<'gram>> + 'a {
    grammar
        .get_nullable_production_matches_by_lhs(nonterminal)
        .filter_map(|matched_production| {
            let term_match = TermMatch::Nonterminal(matched_production.clone());
            traversal.match_term(term_match)
        })
}

fn scan<'gram>(
    traversal: &Traversal<'gram>,
    terminal: &'gram str,
) -> impl Iterator<Item = Traversal<'gram>> {
    let scanned = if traversal.input_range.next().starts_with(terminal) {
        let term_match = TermMatch::Terminal(terminal);
        traversal.match_term(term_match)
    } else {
        None
    };

    scanned.into_iter()
}

fn complete<'gram, 'a>(
    complete_traversal: &'a Traversal<'gram>,
    prod_match: &'a Rc<ProductionMatch<'gram>>,
    incomplete: &'a TermCompletionMap<'gram>,
    arena: &'a crate::append_vec::AppendOnlyVec<Traversal<'gram>, TraversalId>,
) -> impl Iterator<Item = Traversal<'gram>> + 'a {
    let incomplete_key =
        TermCompletionKey::new(prod_match.lhs, complete_traversal.input_range.offset.start);

    incomplete
        .get(&incomplete_key)
        .into_iter()
        .flatten()
        .filter_map(|id| {
            let term_match = TermMatch::Nonterminal(prod_match.clone());
            arena
                .get(*id)
                .and_then(|traversal| traversal.match_term(term_match))
        })
}

struct ParseIter<'gram> {
    grammar: Rc<GrammarMatching<'gram>>,
    traversal_queue: TraversalQueue<'gram>,
    incomplete: TermCompletionMap<'gram>,
}

impl<'gram> ParseIter<'gram> {
    pub fn new(grammar: Rc<GrammarMatching<'gram>>, input: &'gram str) -> Self {
        let input_range = InputRange::new(input);
        let traversal_queue = TraversalQueue::new(&grammar, input_range);

        Self {
            grammar,
            traversal_queue,
            incomplete: Default::default(),
        }
    }
    fn parse_tree(prod_match: Rc<ProductionMatch<'gram>>) -> ParseTree<'gram> {
        let rhs = prod_match
            .rhs
            .iter()
            .map(|term_match| match term_match {
                TermMatch::Terminal(term) => ParseTreeNode::Terminal(term),
                TermMatch::Nonterminal(prod_match) => {
                    ParseTreeNode::Nonterminal(Self::parse_tree(prod_match.clone()))
                }
            })
            .collect::<Vec<ParseTreeNode>>();

        ParseTree::new(prod_match.lhs, rhs)
    }
}

impl<'gram> Iterator for ParseIter<'gram> {
    type Item = ParseTree<'gram>;

    fn next(&mut self) -> Option<Self::Item> {
        let _span = tracing::span!(tracing::Level::TRACE, "ParseIter::next").entered();
        let starting_prod_match = self.traversal_queue.handle_pop(|id, arena, created| {
            let _span = tracing::span!(tracing::Level::TRACE, "ParseIter::handler").entered();
            let traversal = arena.get(id).expect("invalid traversal ID");

            match traversal.earley() {
                EarleyStep::Predict(nonterminal) => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Predict").entered();
                    created.extend(predict(traversal, nonterminal, &self.grammar));
                    created.extend(complete_nullable(traversal, nonterminal, &self.grammar));

                    let incomplete_key = TermCompletionKey::new(
                        nonterminal,
                        traversal.input_range.offset.total_len(),
                    );

                    self.incomplete.entry(incomplete_key).or_default().push(id);
                }
                EarleyStep::Scan(terminal) => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Scan").entered();
                    created.extend(scan(traversal, terminal));
                }
                EarleyStep::Complete(prod_match) => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Complete").entered();
                    created.extend(complete(traversal, &prod_match, &self.incomplete, arena));

                    {
                        let _span =
                            tracing::span!(tracing::Level::TRACE, "full_prod_match").entered();

                        let is_full_traversal = traversal.input_range.is_complete()
                            && self
                                .grammar
                                .is_starting_prod_id(&traversal.matching.prod_id);

                        if is_full_traversal {
                            return Some(prod_match);
                        }
                    }
                }
            }

            None
        });

        {
            let _span = tracing::span!(tracing::Level::TRACE, "ParseIter::parse_tree").entered();
            starting_prod_match.map(Self::parse_tree)
        }
    }
}

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input: &'gram str,
) -> impl Iterator<Item = ParseTree<'gram>> {
    let _span = tracing::span!(tracing::Level::TRACE, "parse").entered();
    let grammar = GrammarMatching::new(grammar);
    let grammar = Rc::new(grammar);
    ParseIter::new(grammar, input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    #[test]
    fn undefined_prod() {
        let grammar: Grammar = "
        <start> ::= <a> | <b>
        <a> ::= 'a'
        "
        .parse()
        .unwrap();

        let input = "a";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn dna_left_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <dna> <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn dna_right_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn ambiguous() {
        let grammar: Grammar = "<start> ::= <a> | <b>
        <a> ::= \"END\"
        <b> ::= \"END\""
            .parse()
            .unwrap();

        let input = "END";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 2);
    }

    #[test]
    fn optional_noop() {
        let grammar: Grammar = "
        <a> ::= <b> | 'a'
        <b> ::= <a>"
            .parse()
            .unwrap();

        let input = "a";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 2);
    }

    #[test]
    fn recursive_nested() {
        let grammar: Grammar = "
            <a> ::= <b> | 'a'
            <b> ::= <a> 
        "
        .parse()
        .unwrap();

        let input = "a";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 2);
    }

    #[test]
    fn empty_right_recursive() {
        let grammar: Grammar = "<a> ::= '' | 'a' <a>".parse().unwrap();

        let input = "aaaaaaaaaa";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn empty_left_recursive() {
        let grammar: Grammar = "<a> ::= '' | <a> 'a'".parse().unwrap();

        let input = "aaaaaaaaaa";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn complete_empty() {
        let grammar: Grammar = "<start> ::= \"hi\" <empty>
        <empty> ::= \"\""
            .parse()
            .unwrap();

        let input = "hi";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn empty() {
        let grammar: Grammar = "<start> ::= \"\"".parse().unwrap();

        let input = "";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn nested_empty_post() {
        let grammar: Grammar = "
        <start> ::= <a> <empty>
        <a> ::= 'a' <empty>
        <empty> ::= ''"
            .parse()
            .unwrap();

        let input = "a";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn nested_empty_pre() {
        let grammar: Grammar = "
        <start> ::= <empty> <a>
        <a> ::= <empty> 'a'
        <empty> ::= ''"
            .parse()
            .unwrap();

        let input = "a";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn nested_empty_pre_and_post() {
        let grammar: Grammar = "
        <start> ::= <empty> <a> <empty>
        <a> ::= <empty> 'a' <empty>
        <empty> ::= ''"
            .parse()
            .unwrap();

        let input = "a";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn empty_inline() {
        let grammar: Grammar = "
        <start> ::= <a> '' <a>
        <a> ::= 'a'"
            .parse()
            .unwrap();

        let input = "aa";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn empty_ambiguous() {
        let grammar: Grammar = "
        <start> ::= <a> | <b>
        <a> ::= ''
        <b> ::= ''"
            .parse()
            .unwrap();

        let input = "";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 2);
    }

    #[test]
    fn optional_whitespace() {
        let grammar: Grammar = "
        <balanced> ::= <left> <balanced> <right>
                     | ''
        
        <left> ::= <opt-ws> '(' <opt-ws>
        <right> ::= <opt-ws> ')' <opt-ws>
        
        <opt-ws> ::= '' | <ws>
        <ws> ::= ' ' | ' ' <ws>
        "
        .parse()
        .unwrap();

        let input = "()";

        assert!(
            grammar.parse_input(input).next().is_some(),
            "can't parse: {input}"
        );
    }

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
            let expr_choice: &mut crate::Expression = expressions[*expr_choice_index];

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

        let mut parses = parse(&grammar.0, input);
        TestResult::from_bool(parses.next().is_some())
    }

    #[test]
    fn empty_rules_allow_parse() {
        QuickCheck::new()
            .tests(1000)
            .quickcheck(prop_empty_rules_allow_parse as fn(NestedEmptyGrammar) -> TestResult)
    }

    // (source: <https://loup-vaillant.fr/tutorials/earley-parsing/empty-rules>)
    #[test]
    fn empty_noop() {
        let grammar: Grammar = "
        <a> ::= '' | <b>
        <b> ::= <a>"
            .parse()
            .unwrap();

        let input = "";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 2);
    }

    // (source: <https://loup-vaillant.fr/tutorials/earley-parsing/recogniser>)
    // Sum     -> Sum     [+-] Product
    // Sum     -> Product
    // Product -> Product [*/] Factor
    // Product -> Factor
    // Factor  -> '(' Sum ')'
    // Factor  -> Number
    // Number  -> [0-9] Number
    // Number  -> [0-9]
    #[test]
    fn math() {
        let grammar: Grammar = "<sum> ::= <sum> <add> <product>
            <sum> ::= <product>
            <product> ::= <product> <mult> <factor>
            <product> ::= <factor>
            <add> ::= \"+\" | \"-\"
            <mult> ::= \"*\" | \"/\"
            <factor> ::= \"(\" <sum> \")\"
            <factor> ::= <number>
            <number> ::= <digit> <number>
            <number> ::= <digit>
            <digit> ::= \"0\" | \"1\" | \"2\" | \"3\" | \"4\" | \"5\" | \"6\" | \"7\" | \"8\" | \"9\"
        ".parse().unwrap();

        let input = "1+(2*3-4)";

        let parses: Vec<_> = parse(&grammar, input).collect();

        let expected_parse_tree = "
<sum> ::= <sum> <add> <product>
├── <sum> ::= <product>
│   └── <product> ::= <factor>
│       └── <factor> ::= <number>
│           └── <number> ::= <digit>
│               └── <digit> ::= \"1\"
│                   └── \"1\"
├── <add> ::= \"+\"
│   └── \"+\"
└── <product> ::= <factor>
    └── <factor> ::= \"(\" <sum> \")\"
        ├── \"(\"
        ├── <sum> ::= <sum> <add> <product>
        │   ├── <sum> ::= <product>
        │   │   └── <product> ::= <product> <mult> <factor>
        │   │       ├── <product> ::= <factor>
        │   │       │   └── <factor> ::= <number>
        │   │       │       └── <number> ::= <digit>
        │   │       │           └── <digit> ::= \"2\"
        │   │       │               └── \"2\"
        │   │       ├── <mult> ::= \"*\"
        │   │       │   └── \"*\"
        │   │       └── <factor> ::= <number>
        │   │           └── <number> ::= <digit>
        │   │               └── <digit> ::= \"3\"
        │   │                   └── \"3\"
        │   ├── <add> ::= \"-\"
        │   │   └── \"-\"
        │   └── <product> ::= <factor>
        │       └── <factor> ::= <number>
        │           └── <number> ::= <digit>
        │               └── <digit> ::= \"4\"
        │                   └── \"4\"
        └── \")\"\n"
            .trim_start();

        assert_eq!(parses.len(), 1);
        let parse_tree = format!("{}", parses[0]);
        assert_eq!(parse_tree, expected_parse_tree)
    }
}
