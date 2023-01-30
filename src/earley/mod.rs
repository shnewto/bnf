mod grammar;
mod input_range;
mod traversal;

use crate::{tracing, ParseTree, ParseTreeNode, Term};
use grammar::{GrammarMatching, Production};
use input_range::InputRange;
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;
use traversal::{TermMatch, Traversal, TraversalId, TraversalTree};

type NullMatchMap<'gram> = std::collections::HashMap<&'gram crate::Term, Vec<ParseTree<'gram>>>;

fn find_null_prod_matches(grammar: Rc<GrammarMatching>) -> NullMatchMap {
    let mut null_matches = NullMatchMap::new();
    let input = "";

    // TODO: can do a work queue of affected productions to save on the happy case, which is common
    for starting_prod in grammar.productions_iter() {
        let starting_term = starting_prod.lhs;
        let is_nullable_productions = false;
        let parses = ParseIter::new(
            grammar.clone(),
            input,
            starting_term,
            is_nullable_productions,
        );

        for parse in parses {
            null_matches.entry(starting_term).or_default().push(parse);
        }
    }

    null_matches
}

/// Key used for "incomplete" [`Traversal`]
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct TermCompletionKey<'gram> {
    term: &'gram Term,
    input_start: usize,
}

impl<'gram> TermCompletionKey<'gram> {
    pub fn new(term: &'gram Term, input_start: usize) -> Self {
        Self { term, input_start }
    }
}

#[derive(Debug, Default)]
pub(crate) struct TraversalCompletionMap<'gram> {
    incomplete: HashMap<TermCompletionKey<'gram>, Vec<TraversalId>>,
    complete: HashMap<TermCompletionKey<'gram>, Vec<TraversalId>>,
}

impl<'gram> TraversalCompletionMap<'gram> {
    pub fn get_incomplete(
        &'_ self,
        term: &'gram Term,
        complete_traversal: &Traversal<'gram>,
    ) -> impl Iterator<Item = TraversalId> + '_ {
        let key = TermCompletionKey::new(term, complete_traversal.input_range.offset.start);
        self.incomplete.get(&key).into_iter().flatten().cloned()
    }
    pub fn insert(&mut self, traversal: &Traversal<'gram>, lhs: &'gram Term) {
        match traversal.next_unmatched() {
            Some(Term::Terminal(_)) => {
                // do nothing, because terminals are irrelevant to completion
            }
            Some(unmatched @ Term::Nonterminal(_)) => {
                let key =
                    TermCompletionKey::new(unmatched, traversal.input_range.offset.total_len());
                self.incomplete.entry(key).or_default().push(traversal.id);
            }
            None => {
                let key = TermCompletionKey::new(lhs, traversal.input_range.offset.start);
                self.complete.entry(key).or_default().push(traversal.id);
            }
        }
    }
}

struct ParseIter<'gram> {
    grammar: Rc<GrammarMatching<'gram>>,
    completion_map: TraversalCompletionMap<'gram>,
    null_match_map: NullMatchMap<'gram>,
    traversal_tree: TraversalTree<'gram>,
    traversal_queue: VecDeque<TraversalId>,
    traversal_processed: HashSet<TraversalId>,
    starting_term: &'gram Term,
}

impl<'gram> ParseIter<'gram> {
    pub fn new(
        grammar: Rc<GrammarMatching<'gram>>,
        input: &'gram str,
        starting_term: &'gram Term,
        is_nullable_productions: bool,
    ) -> Self {
        let input_range = InputRange::new(input);
        let mut traversal_queue = VecDeque::<TraversalId>::default();
        let mut traversal_processed = HashSet::<TraversalId>::default();
        let mut traversal_tree = TraversalTree::default();

        for starting_prod in grammar.get_productions_by_lhs(starting_term) {
            let traversal = traversal_tree.predict(starting_prod, &input_range);
            traversal_queue.push_back(traversal.id);
            traversal_processed.insert(traversal.id);
        }

        let mut parse_iter = Self {
            grammar,
            starting_term,
            completion_map: Default::default(),
            null_match_map: NullMatchMap::new(),
            traversal_tree,
            traversal_queue,
            traversal_processed,
        };

        if is_nullable_productions {
            // parse_iter.find_nullable_productions();
        }

        parse_iter
    }
    fn earley(&mut self) -> Option<TraversalId> {
        while let Some(traversal_id) = self.traversal_queue.pop_front() {
            // println!("{:#?}", self.traversal_tree.get(traversal_id));
            match self.traversal_tree.get_matching(traversal_id) {
                Some(nonterminal @ Term::Nonterminal(_)) => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Predict").entered();

                    let traversal = self.traversal_tree.get(traversal_id);
                    let lhs = self
                        .grammar
                        .get_production_by_id(traversal.production_id)
                        .lhs;

                    self.completion_map.insert(traversal, lhs);

                    let input_range = traversal.input_range.clone();
                    for production in self.grammar.get_productions_by_lhs(nonterminal) {
                        let predicted = self.traversal_tree.predict(production, &input_range);
                        if self.traversal_processed.insert(predicted.id) {
                            // println!("predicted {:?}", predicted);
                            self.traversal_queue.push_back(predicted.id);
                        }
                    }

                    // TODO: null match completions, cant be parse trees
                    for _null_match in self.null_match_map.get(lhs).into_iter().flatten() {}
                }
                Some(Term::Terminal(term)) => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Scan").entered();
                    let traversal = self.traversal_tree.get(traversal_id);
                    if traversal.input_range.next().starts_with(term) {
                        let term_match = TermMatch::Terminal(term);
                        let scanned = self.traversal_tree.match_term(traversal_id, term_match);
                        if self.traversal_processed.insert(scanned.id) {
                            // println!("scanned {:?}", scanned);
                            self.traversal_queue.push_back(scanned.id);
                        }
                    }
                }
                None => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Complete").entered();

                    let traversal = self.traversal_tree.get(traversal_id);
                    let lhs = self
                        .grammar
                        .get_production_by_id(traversal.production_id)
                        .lhs;

                    let is_full_traversal =
                        traversal.input_range.is_complete() && lhs == self.starting_term;

                    for incomplete_traversal_id in
                        self.completion_map.get_incomplete(lhs, traversal)
                    {
                        let term_match = TermMatch::Nonterminal(traversal_id);
                        let completed = self
                            .traversal_tree
                            .match_term(incomplete_traversal_id, term_match);
                        if self.traversal_processed.insert(completed.id) {
                            // println!("completed {:?}", completed);
                            self.traversal_queue.push_back(completed.id);
                        }
                    }

                    if is_full_traversal {
                        return Some(traversal_id);
                    }
                }
            }
        }

        None
    }
}

impl<'gram> Iterator for ParseIter<'gram> {
    type Item = ParseTree<'gram>;

    fn next(&mut self) -> Option<Self::Item> {
        let _span = tracing::span!(tracing::Level::TRACE, "ParseIter_next").entered();

        self.earley()
            .map(|traversal_id| parse_tree(&self.traversal_tree, &self.grammar, traversal_id))
    }
}

fn parse_tree<'gram>(
    tree: &TraversalTree<'gram>,
    grammar: &GrammarMatching<'gram>,
    traversal_id: TraversalId,
) -> ParseTree<'gram> {
    let production = {
        let traversal = tree.get(traversal_id);
        grammar.get_production_by_id(traversal.production_id)
    };
    let rhs = tree
        .get_matched(traversal_id)
        .map(|term_match| match term_match {
            TermMatch::Terminal(term) => ParseTreeNode::Terminal(term),
            TermMatch::Nonterminal(traversal_id) => {
                ParseTreeNode::Nonterminal(parse_tree(tree, grammar, *traversal_id))
            }
        })
        .collect::<Vec<ParseTreeNode>>();

    ParseTree::new(production.lhs, rhs)
}

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input: &'gram str,
) -> impl Iterator<Item = ParseTree<'gram>> {
    let _span = tracing::span!(tracing::Level::TRACE, "parse").entered();

    let starting_term = grammar
        .starting_term()
        .expect("Grammar must have one production to parse");

    let grammar = GrammarMatching::new(grammar);
    let grammar = Rc::new(grammar);

    let is_nullable_productions = true;

    ParseIter::new(grammar, input, starting_term, is_nullable_productions)
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
    fn recursive_nested_infinite() {
        let grammar: Grammar = "
            <a> ::= <b> | 'z'
            <b> ::= <a> 
        "
        .parse()
        .unwrap();

        let input = "z";

        // there are infinite parses to this, so take the first 100 and call it good
        // TODO: why does stack explode so quickly?
        let parse_count = 100;
        let parses = parse(&grammar, input).take(parse_count);
        assert_eq!(parses.count(), parse_count);
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
    fn empty_first_nested() {
        // this structure exposes improper "nullable" production detection
        let grammar: Grammar = "
        <a> ::= '' | '' <b> <c>
        <b> ::= <c>
        <c> ::= <a>
        "
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

    #[test]
    fn qualified_whitespace() {
        let grammar: Grammar = "
        <terms> ::= <terms> <ws> <term>
                  | <term>
        <term> ::= <qualified>
                 | 'unqualified'
        <qualified> ::= 'QUALIFIER:' <qual-term>
        <qual-term> ::= <qual-term> <ws>
                      | 'qualified'
        <ws> ::= ' ' | ' ' <ws>
        "
        .parse()
        .unwrap();

        let input = "QUALIFIER:qualified unqualified";

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
