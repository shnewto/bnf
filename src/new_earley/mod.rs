mod grammar;
mod input_range;
mod traversal;

use crate::{ParseTree, ParseTreeNode, Term};
use grammar::{GrammarMatching, ProductionMatch, TermMatch};
use input_range::InputRange;
use std::collections::HashMap;
use std::rc::Rc;
use traversal::{EarleyStep, Traversal, TraversalCompletionQueue};

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

type TermCompletionMap<'gram> = HashMap<TermCompletionKey<'gram>, Vec<Traversal<'gram>>>;

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
            // TODO: avoid clone
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
    prod_match: &'a ProductionMatch<'gram>,
    incomplete: &'a TermCompletionMap<'gram>,
) -> impl Iterator<Item = Traversal<'gram>> + 'a {
    let incomplete_key =
        TermCompletionKey::new(prod_match.lhs, complete_traversal.input_range.offset.start);

    incomplete
        .get(&incomplete_key)
        .into_iter()
        .flatten()
        .filter_map(|traversal| {
            // TODO: avoid clone
            let term_match = TermMatch::Nonterminal(prod_match.clone());
            traversal.match_term(term_match)
        })
}

#[derive(Debug)]
pub struct EarleyParser<'gram> {
    grammar: Rc<GrammarMatching<'gram>>,
}

impl<'gram> EarleyParser<'gram> {
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
        let grammar = GrammarMatching::new(grammar);
        let grammar = Rc::new(grammar);
        Self { grammar }
    }
    pub fn parse<'a>(&'a self, input: &'gram str) -> impl Iterator<Item = ParseTree<'gram>> + 'a {
        ParseIter::new(self.grammar.clone(), input)
    }
}

struct ParseIter<'gram> {
    grammar: Rc<GrammarMatching<'gram>>,
    traversal_queue: TraversalCompletionQueue<'gram>,
    incomplete: TermCompletionMap<'gram>,
}

impl<'gram> ParseIter<'gram> {
    pub fn new<'a>(grammar: Rc<GrammarMatching<'gram>>, input: &'gram str) -> Self {
        let input_range = InputRange::new(input);
        let traversal_queue = TraversalCompletionQueue::new(&grammar, input_range);

        Self {
            grammar,
            traversal_queue,
            incomplete: Default::default(),
        }
    }
    fn parse_tree(&self, prod_match: ProductionMatch<'gram>) -> ParseTree<'gram> {
        let rhs = prod_match
            .rhs
            .into_iter()
            .map(|term_match| match term_match {
                TermMatch::Terminal(term) => ParseTreeNode::Terminal(term),
                TermMatch::Nonterminal(prod_match) => {
                    ParseTreeNode::Nonterminal(self.parse_tree(prod_match))
                }
            })
            .collect();

        ParseTree::new(prod_match.lhs, rhs)
    }
}

impl<'gram> Iterator for ParseIter<'gram> {
    type Item = ParseTree<'gram>;

    fn next(&mut self) -> Option<Self::Item> {
        let starting_prod_match = self.traversal_queue.handle_pop(|traversal| {
            let mut created = Vec::<Traversal>::new();
            match traversal.earley() {
                EarleyStep::Predict(nonterminal) => {
                    created.extend(predict(&traversal, nonterminal, &self.grammar));
                    created.extend(complete_nullable(&traversal, nonterminal, &self.grammar));

                    let incomplete_key = TermCompletionKey::new(
                        nonterminal,
                        traversal.input_range.offset.total_len(),
                    );

                    self.incomplete
                        .entry(incomplete_key)
                        .or_default()
                        .push(traversal);
                }
                EarleyStep::Scan(terminal) => {
                    created.extend(scan(&traversal, terminal));
                }
                EarleyStep::Complete(prod_match) => {
                    created.extend(complete(&traversal, &prod_match, &self.incomplete));
                }
            }
            created.into_iter()
        });

        starting_prod_match.map(|prod_match| self.parse_tree(prod_match))
    }
}

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input: &'gram str,
) -> impl Iterator<Item = ParseTree<'gram>> {
    let grammar = GrammarMatching::new(grammar);
    let grammar = Rc::new(grammar);
    ParseIter::new(grammar, input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;

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

        let tree = parse(&grammar, input).next().unwrap();
        println!("{tree}");
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

    // TODO: test case for <start> ::= <a> | <b>, with both <a> and <b> nullable should give two parses
    // TODO: test case for <nonterm> without a rule
    // TODO: property test which inserts empty rule terms and should still parse

    // (source: <https://loup-vaillant.fr/tutorials/earley-parsing/empty-rules>)
    #[test]
    fn empty_infinite() {
        let grammar: Grammar = "
        <a> ::= '' | <b>
        <b> ::= <a>"
            .parse()
            .unwrap();

        let input = "";

        // take first 100 parses of infinite parse iterator
        let parses = parse(&grammar, input).take(100);
        assert_eq!(parses.count(), 100);

        println!("input: '{input}'");
        let mut parses = parse(&grammar, input).take(100);
        while let Some(parse) = parses.next() {
            println!("{parse}")
        }
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
