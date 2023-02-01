mod grammar;
mod input_range;
mod traversal;

use crate::{tracing, ParseTree, ParseTreeNode, Term};
use grammar::{ParseGrammar, Production};
use input_range::InputRange;
use std::collections::{HashMap, HashSet, VecDeque};
use traversal::{TermMatch, Traversal, TraversalId, TraversalTree};

pub fn parse<'gram>(
    grammar: &'gram crate::Grammar,
    input: &'gram str,
) -> impl Iterator<Item = ParseTree<'gram>> {
    let starting_term = grammar
        .starting_term()
        .expect("Grammar must have one production to parse");

    let grammar = ParseGrammar::new(grammar);

    let traversal_tree = TraversalTree::default();

    ParseTreeIter::new(traversal_tree, input, grammar, starting_term)
}

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
}

fn parse_tree<'gram>(
    traversal_tree: &TraversalTree<'gram>,
    grammar: &ParseGrammar<'gram>,
    traversal_id: TraversalId,
) -> ParseTree<'gram> {
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

fn init_traversal_queue<'gram>(
    traversal_tree: &mut TraversalTree<'gram>,
    queue: &mut TraversalQueue,
    grammar: &ParseGrammar<'gram>,
    starting_term: &'gram Term,
    input: &InputRange<'gram>,
) {
    println!("init queue: {input:?}, {starting_term}");
    for starting_prod in grammar.get_productions_by_lhs(starting_term) {
        let traversal = traversal_tree.predict_starting(starting_prod, &input);
        println!("predicted starting {:?}", traversal);
        queue.push_back(traversal.id);
    }
}

fn earley<'gram>(
    queue: &mut TraversalQueue,
    traversal_tree: &mut TraversalTree<'gram>,
    completions: &mut CompletionMap<'gram>,
    grammar: &ParseGrammar<'gram>,
) -> Option<TraversalId> {
    while let Some(traversal_id) = queue.pop_front() {
        println!("{grammar:#?}");
        println!("{:#?}", traversal_tree.get(traversal_id));

        match traversal_tree.get_matching(traversal_id) {
            Some(nonterminal @ Term::Nonterminal(_)) => {
                let _span = tracing::span!(tracing::Level::TRACE, "Predict").entered();

                let traversal = traversal_tree.get(traversal_id);
                let lhs = grammar.get_production_by_id(traversal.production_id).lhs;

                completions.insert(traversal, lhs);

                let input_range = traversal.input_range.clone();

                for production in grammar.get_productions_by_lhs(nonterminal) {
                    let predicted = traversal_tree.predict(production, &input_range);
                    println!("predicted {:?}", predicted);
                    queue.push_back(predicted.id);
                }

                for completed in completions.get_complete(nonterminal, &input_range) {
                    let term_match = TermMatch::Nonterminal(completed);
                    let prior_completed = traversal_tree.match_term(traversal_id, term_match);
                    println!("prior_completed {:?}", prior_completed);
                    queue.push_back(prior_completed.id);
                }

                // for null_match in nullable_map.get(nonterminal).into_iter().flatten() {
                //     let term_match = TermMatch::Nonterminal(*null_match);
                //     let null_completed = traversal_tree.match_term(traversal_id, term_match);
                //     println!("null_completed {:?}", null_completed);
                //     queue.push_back(null_completed.id);
                // }
            }
            Some(Term::Terminal(term)) => {
                let _span = tracing::span!(tracing::Level::TRACE, "Scan").entered();
                let traversal = traversal_tree.get(traversal_id);
                if traversal.input_range.next().starts_with(term) {
                    let term_match = TermMatch::Terminal(term);
                    let scanned = traversal_tree.match_term(traversal_id, term_match);
                    println!("scanned {:?}", scanned);
                    queue.push_back(scanned.id);
                }
            }
            None => {
                let _span = tracing::span!(tracing::Level::TRACE, "Complete").entered();

                let traversal = traversal_tree.get(traversal_id);
                let is_full_traversal =
                    traversal.is_starting && traversal.input_range.is_complete();
                let lhs = grammar.get_production_by_id(traversal.production_id).lhs;

                completions.insert(traversal, lhs);

                for incomplete_traversal_id in completions.get_incomplete(lhs, traversal) {
                    let term_match = TermMatch::Nonterminal(traversal_id);
                    let completed = traversal_tree.match_term(incomplete_traversal_id, term_match);

                    println!("completed {:?}", completed);
                    queue.push_back(completed.id);
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
    traversal_tree: TraversalTree<'gram>,
    grammar: ParseGrammar<'gram>,
    queue: TraversalQueue,
    completions: CompletionMap<'gram>,
}

impl<'gram> ParseTreeIter<'gram> {
    pub fn new(
        mut traversal_tree: TraversalTree<'gram>,
        input: &'gram str,
        grammar: ParseGrammar<'gram>,
        starting_term: &'gram Term,
    ) -> Self {
        let input = InputRange::new(input);
        let mut queue = TraversalQueue::default();

        init_traversal_queue(
            &mut traversal_tree,
            &mut queue,
            &grammar,
            starting_term,
            &input,
        );

        Self {
            traversal_tree,
            grammar,
            queue,
            completions: Default::default(),
        }
    }
}

impl<'gram> Iterator for ParseTreeIter<'gram> {
    type Item = ParseTree<'gram>;
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            queue,
            completions,
            grammar,
            traversal_tree,
        } = self;

        earley(queue, traversal_tree, completions, grammar).map(|traversal_id| {
            let tree = parse_tree(&traversal_tree, &grammar, traversal_id);
            println!("ParseTree\n{tree}");
            tree
        })
    }
}

#[derive(Debug)]
struct ParseIter<'gram, 'p> {
    traversal_tree: &'p mut TraversalTree<'gram>,
    grammar: &'p ParseGrammar<'gram>,
    queue: TraversalQueue,
    completions: CompletionMap<'gram>,
}

impl<'gram, 'p> ParseIter<'gram, 'p> {
    pub fn new(
        traversal_tree: &'p mut TraversalTree<'gram>,
        input: &'gram str,
        grammar: &'p ParseGrammar<'gram>,
        starting_term: &'gram Term,
    ) -> Self {
        let input = InputRange::new(input);
        let mut queue = TraversalQueue::default();

        init_traversal_queue(traversal_tree, &mut queue, grammar, starting_term, &input);

        Self {
            traversal_tree,
            grammar,
            queue,
            completions: Default::default(),
        }
    }
}

impl<'gram, 'p> Iterator for ParseIter<'gram, 'p> {
    type Item = TraversalId;

    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            queue,
            completions,
            grammar,
            traversal_tree,
        } = self;

        earley(queue, traversal_tree, completions, grammar)
    }
}

/// Key used for "incomplete" [`Traversal`]
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct CompletionKey<'gram> {
    term: &'gram Term,
    input_start: usize,
}

impl<'gram> CompletionKey<'gram> {
    pub fn new_start(term: &'gram Term, input: &InputRange<'gram>) -> Self {
        Self {
            term,
            input_start: input.offset.start,
        }
    }
    pub fn new_total(term: &'gram Term, input: &InputRange<'gram>) -> Self {
        Self {
            term,
            input_start: input.offset.total_len(),
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct CompletionMap<'gram> {
    incomplete: HashMap<CompletionKey<'gram>, HashSet<TraversalId>>,
    complete: HashMap<CompletionKey<'gram>, HashSet<TraversalId>>,
}

impl<'gram> CompletionMap<'gram> {
    pub fn get_incomplete(
        &'_ self,
        term: &'gram Term,
        complete_traversal: &Traversal<'gram>,
    ) -> impl Iterator<Item = TraversalId> + '_ {
        let key = CompletionKey::new_start(term, &complete_traversal.input_range);
        self.incomplete.get(&key).into_iter().flatten().cloned()
    }
    pub fn get_complete(
        &'_ self,
        term: &'gram Term,
        input_range: &InputRange<'gram>,
    ) -> impl Iterator<Item = TraversalId> + '_ {
        let key = CompletionKey::new_total(term, &input_range);
        self.complete.get(&key).into_iter().flatten().cloned()
    }
    pub fn insert(&mut self, traversal: &Traversal<'gram>, lhs: &'gram Term) {
        match traversal.next_unmatched() {
            Some(Term::Terminal(_)) => {
                // do nothing, because terminals are irrelevant to completion
            }
            Some(unmatched @ Term::Nonterminal(_)) => {
                let key = CompletionKey::new_total(unmatched, &traversal.input_range);
                self.incomplete.entry(key).or_default().insert(traversal.id);
            }
            None => {
                let key = CompletionKey::new_start(lhs, &traversal.input_range);
                self.complete.entry(key).or_default().insert(traversal.id);
            }
        }
    }
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

        let parse_count = 100;
        let parses = parse(&grammar, input).take(parse_count);
        assert_eq!(parses.count(), parse_count);
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
    fn empty_noop_infinite() {
        let grammar: Grammar = "
        <a> ::= '' | <b>
        <b> ::= <a>"
            .parse()
            .unwrap();

        let input = "";

        let parse_count = 100;
        let parses = parse(&grammar, input).take(parse_count);
        assert_eq!(parses.count(), parse_count);
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
