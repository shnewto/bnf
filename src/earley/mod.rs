mod grammar;
mod input_range;
mod traversal;
mod traversal_new;

use crate::{tracing, ParseTree, ParseTreeNode, Term};
use grammar::{GrammarMatching, Production, ProductionMatch};
use input_range::InputRange;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
use traversal_new::{TermMatch, Traversal, TraversalId, TraversalTree};

// fn predict<'gram, 'a>(
//     traversal: &'a Traversal<'gram>,
//     nonterminal: &'gram Term,
//     grammar: &'a GrammarMatching<'gram>,
// ) -> impl Iterator<Item = Traversal<'gram>> + 'a {
//     grammar
//         .get_productions_by_lhs(nonterminal)
//         .map(|prod| Traversal::start_production(prod, &traversal.input_range))
// }

// // TODO: maybe no longer needed after TraversalTree
// fn complete_prior<'gram, 'a>(
//     incomplete_traversal: &'a Traversal<'gram>,
//     matching: &'gram Term,
//     completion_map: &'a TraversalCompletionMap<'gram>,
// ) -> impl Iterator<Item = Traversal<'gram>> + 'a {
//     completion_map
//         .get_complete(matching, &incomplete_traversal.input_range)
//         .filter_map(|term_match| {
//             incomplete_traversal.match_term(TermMatch::Nonterminal(term_match))
//         })
// }

// fn complete_nullable<'gram, 'a>(
//     traversal: &'a Traversal<'gram>,
//     nonterminal: &'gram Term,
//     null_match_map: &'a NullMatchMap<'gram>,
// ) -> impl Iterator<Item = Traversal<'gram>> + 'a {
//     null_match_map
//         .get(nonterminal)
//         .into_iter()
//         .flatten()
//         .filter_map(|matched_production| {
//             let term_match = TermMatch::Nonterminal(matched_production.clone());
//             traversal.match_term(term_match)
//         })
// }

// fn scan<'gram>(
//     traversal: &Traversal<'gram>,
//     terminal: &'gram str,
// ) -> impl Iterator<Item = Traversal<'gram>> {
//     let scanned = if traversal.input_range.next().starts_with(terminal) {
//         let term_match = TermMatch::Terminal(terminal);
//         traversal.match_term(term_match)
//     } else {
//         None
//     };

//     scanned.into_iter()
// }

// fn complete<'gram, 'a>(
//     complete_traversal: &'a Traversal<'gram>,
//     prod_match: &'a Rc<ProductionMatch<'gram>>,
//     arena: &'a crate::append_vec::AppendOnlyVec<Traversal<'gram>, TraversalId>,
//     completion_map: &'a TraversalCompletionMap<'gram>,
// ) -> impl Iterator<Item = Traversal<'gram>> + 'a {
//     completion_map
//         .get_incomplete(complete_traversal)
//         .filter_map(|id| {
//             let term_match = TermMatch::Nonterminal(prod_match.clone());

//             arena
//                 .get(id)
//                 .and_then(|traversal| traversal.match_term(term_match))
//         })
// }

type NullMatchMap<'gram> =
    std::collections::HashMap<&'gram crate::Term, Vec<Rc<ProductionMatch<'gram>>>>;

fn find_null_prod_matches(grammar: Rc<GrammarMatching>) -> NullMatchMap {
    let mut null_matches = NullMatchMap::new();
    let input = "";

    // TODO: can do a work queue of affected productions to save on the happy case, which is common
    for starting_prod in grammar.productions_iter() {
        let starting_term = starting_prod.lhs;
        let is_nullable_productions = false;
        let parses = crate::earley::parse_matching(
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

// fn parse_tree(prod_match: Rc<ProductionMatch>) -> ParseTree {
//     let rhs = prod_match
//         .rhs
//         .iter()
//         .map(|term_match| match term_match {
//             TermMatch::Terminal(term) => ParseTreeNode::Terminal(term),
//             TermMatch::Nonterminal(prod_match) => {
//                 ParseTreeNode::Nonterminal(parse_tree(prod_match.clone()))
//             }
//         })
//         .collect::<Vec<ParseTreeNode>>();
//
//     ParseTree::new(prod_match.lhs, rhs)
// }

struct ParseIter<'gram> {
    grammar: Rc<GrammarMatching<'gram>>,
    incomplete_map: HashMap<&'gram Term, Vec<TraversalId>>,
    null_match_map: NullMatchMap<'gram>,
    traversal_tree: TraversalTree<'gram>,
    traversal_queue: VecDeque<TraversalId>,
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
        let null_match_map = if is_nullable_productions {
            find_null_prod_matches(grammar.clone())
        } else {
            NullMatchMap::new()
        };

        if is_nullable_productions {
            tracing::event!(
                tracing::Level::TRACE,
                "grammar nullable terms: {null_match_map:#?}"
            );
        }

        let mut traversal_queue = std::collections::VecDeque::<TraversalId>::default();
        let mut traversal_tree = TraversalTree::default();

        for starting_prod in grammar.get_productions_by_lhs(starting_term) {
            let traversal = traversal_tree.predict(starting_prod, &input_range);
            traversal_queue.push_back(traversal.id);
        }

        Self {
            grammar,
            starting_term,
            incomplete_map: Default::default(),
            null_match_map,
            traversal_tree,
            traversal_queue,
        }
    }
}

impl<'gram> Iterator for ParseIter<'gram> {
    type Item = Rc<ProductionMatch<'gram>>;

    fn next(&mut self) -> Option<Self::Item> {
        let _span = tracing::span!(tracing::Level::TRACE, "ParseIter_next").entered();

        while let Some(traversal_id) = self.traversal_queue.pop_front() {
            match self.traversal_tree.get_matching(traversal_id) {
                Some(nonterminal @ Term::Nonterminal(_)) => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Predict").entered();

                    self.incomplete_map
                        .entry(nonterminal)
                        .or_default()
                        .push(traversal_id);

                    let input_range = self.traversal_tree.get(traversal_id).input_range.after();
                    for production in self.grammar.get_productions_by_lhs(nonterminal) {
                        let predicted = self.traversal_tree.predict(production, &input_range);
                        self.traversal_queue.push_back(predicted.id);
                    }
                }
                Some(Term::Terminal(term)) => {
                    let _span = tracing::span!(tracing::Level::TRACE, "Scan").entered();
                    let traversal = self.traversal_tree.get(traversal_id);
                    if traversal.input_range.next().starts_with(term) {
                        let term_match = TermMatch::Terminal(term);
                        let scanned = self.traversal_tree.match_term(traversal_id, term_match);
                        self.traversal_queue.push_back(scanned.id);
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

                    if let Some(incomplete_traversals) = self.incomplete_map.get(lhs) {
                        for incomplete_traversal_id in incomplete_traversals {
                            let term_match = TermMatch::Nonterminal(traversal_id);
                            let completed = self
                                .traversal_tree
                                .match_term(*incomplete_traversal_id, term_match);
                            self.traversal_queue.push_back(completed.id);
                        }
                    }

                    if is_full_traversal {
                        // return Some(prod_match);
                    }
                }
            }
        }
        None
    }
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

    // parse_matching(grammar, input, starting_term, is_nullable_productions).map(parse_tree)
    std::iter::empty()
}

pub(crate) fn parse_matching<'gram>(
    grammar: Rc<GrammarMatching<'gram>>,
    input: &'gram str,
    starting_term: &'gram Term,
    is_nullable_productions: bool,
) -> impl Iterator<Item = Rc<ProductionMatch<'gram>>> {
    let _span = tracing::span!(tracing::Level::TRACE, "parse_matching").entered();

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

        for parse in &parses {
            println!("{parse}");
        }

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
