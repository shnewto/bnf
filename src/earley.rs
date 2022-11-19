use crate::{
    append_vec::AppendOnlyVec,
    grammar::{ParseTree, ParseTreeNode},
    Term,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ProductionId(usize);

impl From<usize> for ProductionId {
    fn from(id: usize) -> Self {
        Self(id)
    }
}

impl From<ProductionId> for usize {
    fn from(id: ProductionId) -> Self {
        id.0
    }
}

/// `crate::Production` offers multiple possible "right hand side" `Expression`s, which is overly flexible for Earley parsing.
/// `earley::Production` is a one-to-one relationship of `Term` -> `Expression`.
#[derive(Debug)]
struct Production<'gram> {
    id: ProductionId,
    lhs: &'gram Term,
    rhs: &'gram crate::Expression,
    rhs_nullable: Option<Vec<TermMatch<'gram>>>,
}

/// `Production`s organized to be queried during parsing.
/// Not to be confused with `crate::Grammar`.
struct Grammar<'gram> {
    starting_production_ids: Vec<ProductionId>,
    productions: AppendOnlyVec<Production<'gram>, ProductionId>,
    production_ids_by_lhs: std::collections::HashMap<&'gram Term, Vec<ProductionId>>,
}

impl<'gram> Grammar<'gram> {
    /// Create a new `Grammar` which references `crate::Grammar`
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
        let starting_term = &grammar
            .productions_iter()
            .next()
            .expect("Grammar must have one production to parse")
            .lhs;

        let mut productions = AppendOnlyVec::<Production, ProductionId>::new();
        type ProdIdMap<'gram> = std::collections::HashMap<&'gram Term, Vec<ProductionId>>;
        let mut production_ids_by_lhs = ProdIdMap::new();
        let mut production_ids_by_rhs = ProdIdMap::new();

        let flat_prod_iter = grammar
            .productions_iter()
            .flat_map(|prod| prod.rhs_iter().map(|rhs| (&prod.lhs, rhs)));

        let mut nullable_queue = Vec::<ProductionId>::new();

        for (lhs, rhs) in flat_prod_iter {
            let prod = productions.push_with_key(|id| {
                let prod = Production {
                    id,
                    lhs,
                    rhs,
                    rhs_nullable: None,
                };
                prod
            });
            let id = prod.id;

            production_ids_by_lhs.entry(lhs).or_default().push(id);

            for rhs in rhs.terms_iter() {
                production_ids_by_rhs.entry(rhs).or_default().push(id);
            }

            let is_rhs_all_empty = rhs.terms_iter().all(|term| match term {
                Term::Terminal(term) if term.is_empty() => true,
                _ => false,
            });

            if is_rhs_all_empty {
                let production = productions.get_mut(id).expect("invalid production ID");

                let empty_string_match = TermMatch::Terminal("");
                let null_matches: Vec<TermMatch> = production
                    .rhs
                    .terms_iter()
                    .map(|_| empty_string_match)
                    .collect();
                production.rhs_nullable = Some(null_matches);

                let nullable_ids = production_ids_by_rhs
                    .get(production.lhs)
                    .into_iter()
                    .flatten();
                nullable_queue.extend(nullable_ids);
            }
        }

        while let Some(id) = nullable_queue.pop() {
            println!("PROD ID {id:?} may be nullable");

            let production = productions.get_mut(id).expect("invalid production ID");

            // TODO
            // let null_matches: Option<Vec<TermMatch>> = production
            //     .rhs
            //     .terms_iter()
            //     .map(|term| match term {
            //         Term::Terminal(term) if term.is_empty() => Some(TermMatch::Terminal("")),
            //         Term::Nonterminal(_) => {
            //             let a = production_ids_by_lhs.get(term);
            //             todo!()
            //         }
            //         _ => None,
            //     })
            //     .collect();
        }

        let starting_production_ids = production_ids_by_lhs
            .get(starting_term)
            .expect("starting Term has no production")
            .clone();

        Self {
            starting_production_ids,
            productions,
            production_ids_by_lhs,
        }
    }
    pub fn starting_iter(&self) -> impl Iterator<Item = &Production<'gram>> {
        self.starting_production_ids
            .iter()
            .filter_map(|id| self.productions.get(*id))
    }
    /// Get `Production` parts by `ProductionId` (useful when building `ParseTree`)
    pub fn get_production_parts_by_id(
        &self,
        prod_id: &ProductionId,
    ) -> (&'gram Term, &'gram crate::Expression) {
        self.productions
            .get(*prod_id)
            .map(|p| (p.lhs, p.rhs))
            .expect("invalid Production ID")
    }
    /// Get `Production` by the LHS `Term` (useful when predicting new `State`)
    pub fn get_productions_by_lhs(
        &self,
        lhs: &'gram Term,
    ) -> impl Iterator<Item = &Production<'gram>> {
        self.production_ids_by_lhs
            .get(lhs)
            .into_iter()
            .flat_map(|v| v.iter())
            .filter_map(|id| self.productions.get(*id))
    }
}

#[derive(Debug)]
struct Terms<'gram> {
    slice: &'gram [Term],
}

impl<'gram> Terms<'gram> {
    pub fn new(slice: &'gram [Term]) -> Self {
        Self { slice }
    }
    pub fn matching(&self) -> Option<&'gram Term> {
        self.slice.get(0)
    }
    pub fn advance_by(&self, step: usize) -> &'gram [Term] {
        &self.slice[step..]
    }
}

/// The input offset where the `State` started matching
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct StateStart(usize);

/// A sliding window over the input strings being parsed.
#[derive(Clone)]
struct InputRange<'gram> {
    input: &'gram str,
    start: usize,
    len: usize,
}

impl<'gram> InputRange<'gram> {
    pub fn new(input: &'gram str) -> Self {
        Self {
            input,
            start: 0,
            len: 0,
        }
    }
    pub fn next(&self) -> Option<&str> {
        let next_idx = self.start + self.len;
        self.input.get(next_idx..)
    }
    pub fn after(&self) -> Self {
        Self {
            input: self.input,
            start: self.start + self.len,
            len: 0,
        }
    }
    pub fn advance_by(&self, step: usize) -> Self {
        let max_len = self.input.len() - self.start;
        Self {
            input: self.input,
            start: self.start,
            len: std::cmp::min(self.len + step, max_len),
        }
    }
    pub fn is_complete(&self) -> bool {
        self.start == 0 && self.len == self.input.len()
    }
}

/// A clear view of `InputRange`, in the format "InputRange(before | current | after)"
/// e.g., "`InputRange`(["1", "+", "("] | ["2"] | ["*", "3", "-", "4", ")"])"
impl<'gram> std::fmt::Debug for InputRange<'gram> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let before = &self.input[..self.start];
        let scanned = &self.input[self.start..][..self.len];
        let after = &self.input[self.start..][self.len..];
        write!(f, "InputRange({:?} | {:?} | {:?})", before, scanned, after)
    }
}

/// A unique ID for `State` in the append only vector
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct StateId(usize);

impl From<usize> for StateId {
    fn from(id: usize) -> Self {
        Self(id)
    }
}

impl From<StateId> for usize {
    fn from(id: StateId) -> Self {
        id.0
    }
}

/// A matched `Term` which has been partially accepted
#[derive(Debug, Clone, Copy)]
enum TermMatch<'gram> {
    /// The `Term` matched with a terminal string
    Terminal(&'gram str),
    /// The `Term` matched with completed non-terminal `State`
    NonTerminal(StateId),
}

/// One state in an Earley parser
#[derive(Debug)]
struct State<'gram> {
    /// LHS `Term` which is being parsed
    lhs: &'gram Term,
    /// matched `Term`s which have already been parsed
    matched_terms: Vec<TermMatch<'gram>>,
    /// unmatched `Term`s which have yet to be parsed
    unmatched_terms: Terms<'gram>,
    /// unique `ProductionId` for which `Production` created this state
    production_id: ProductionId,
    /// input text range which is being parsed
    input_range: InputRange<'gram>,
}

impl<'gram> State<'gram> {
    /// Create new `State` without advancing matched/unmatched `Term`s
    pub fn new(
        lhs: &'gram Term,
        production_id: ProductionId,
        unmatched_terms: &'gram [Term],
        input_range: InputRange<'gram>,
    ) -> Self {
        let matched_terms = Vec::with_capacity(0);
        let unmatched_terms = Terms::new(unmatched_terms);
        Self {
            lhs,
            matched_terms,
            unmatched_terms,
            production_id,
            input_range,
        }
    }
    /// Create a new `State` by advancing matched/unmatched `Term`s
    pub fn new_term_match(
        state: &State<'gram>,
        matched_term: TermMatch<'gram>,
        input_range_step: usize,
    ) -> Self {
        let mut matched_terms = Vec::with_capacity(state.matched_terms.len() + 1);
        matched_terms.extend_from_slice(&state.matched_terms);
        matched_terms.push(matched_term);

        Self {
            lhs: state.lhs,
            matched_terms,
            unmatched_terms: Terms::new(state.unmatched_terms.advance_by(1)),
            production_id: state.production_id.clone(),
            input_range: state.input_range.advance_by(input_range_step),
        }
    }
    /// If the `State` has scanned the full input text AND originates from a starting production
    /// then it is a complete parse
    pub fn is_complete(&self, starting_prod_ids: &[ProductionId]) -> bool {
        starting_prod_ids.contains(&self.production_id) && self.input_range.is_complete()
    }
}

/// Create new `State` by finding `Production` with the current matching `Term` on the LHS
fn predict<'gram, 'a>(
    matching: &'gram Term,
    input_range: &'a InputRange<'gram>,
    grammar: &'a Grammar<'gram>,
) -> impl Iterator<Item = State<'gram>> + 'a {
    grammar.get_productions_by_lhs(matching).map(|prod| {
        State::new(
            prod.lhs,
            prod.id.clone(),
            &prod.rhs.terms,
            input_range.after(),
        )
    })
}

/// TODO
fn predict_nullable<'gram, 'a>(
    matching: &'gram Term,
    input_range: &'a InputRange<'gram>,
    grammar: &'a Grammar<'gram>,
) -> impl Iterator<Item = State<'gram>> + 'a {
    // TODO
    std::iter::empty()
}

/// Create new `State` if the current matching `Term` matches the next inpu text
fn scan<'gram, 'a>(state: &'a State<'gram>) -> impl Iterator<Item = State<'gram>> {
    state
        .unmatched_terms
        .matching()
        .zip(state.input_range.next())
        .and_then(|(matching, next_input)| match matching {
            Term::Terminal(term) if next_input.starts_with(term) => Some(term),
            _ => None,
        })
        .map(|term| {
            let term_match = TermMatch::Terminal(term);
            State::new_term_match(state, term_match, term.len())
        })
        .into_iter()
}

/// Create new `State` by finding incomplete `State`s which are pending on another `State`.
///
/// For example, given a pending Earley state "<dna> ::= • <base>" (<dna> is pending on <base>)
/// and a completed Earley state "<base> ::= 'A' •".
///
/// Then we say "<dna> ::= • <base>" is *completed* by "<base> ::= 'A' •",
/// which yields a new state: "<dna> ::= <base> •"
///
/// Note: An `State` can only be completed by another `State` with matching `StateStart`, the offset where the state is matching.
/// This has been omitted from this example, but must be respected in real parsing.
fn complete<'gram, 'a>(
    key: StateId,
    input_range: &'a InputRange<'gram>,
    parent: &'a State<'gram>,
) -> State<'gram> {
    let term_match = TermMatch::NonTerminal(key);
    State::new_term_match(parent, term_match, input_range.len)
}

/// Earley parsing will attempt to repeat states. If not de-duplicated, this causes infinite parsing loops as well as useless processing.
/// New `State`s are de-duplicated by `StateProcessingKey`,
/// which is a combination of `InputRange`, `ProductionId`, and unmatched `Term`s.
#[derive(Debug, PartialEq, Eq, Hash)]
struct StateProcessingKey {
    input_start: usize,
    input_len: usize,
    production_id: ProductionId,
    unmatched_term_len: usize,
}

impl<'gram> StateProcessingKey {
    pub fn from_state(state: &State<'gram>) -> Self {
        Self {
            input_start: state.input_range.start,
            input_len: state.input_range.len,
            production_id: state.production_id.clone(),
            unmatched_term_len: state.unmatched_terms.slice.len(),
        }
    }
}

/// When completing `State`s, used to find matching `State`s
#[derive(Debug, PartialEq, Eq, Hash)]
struct StateCompletionKey<'gram> {
    state_start: StateStart,
    term: Option<&'gram Term>,
}

impl<'gram> StateCompletionKey<'gram> {
    pub fn from_state(state: &State<'gram>) -> Self {
        let state_start = StateStart(state.input_range.start + state.input_range.len);
        let term = state.unmatched_terms.matching();
        Self { state_start, term }
    }
    pub fn from_complete(state: &State<'gram>) -> Self {
        let state_start = StateStart(state.input_range.start);
        let term = Some(state.lhs);
        Self { state_start, term }
    }
}

/// De-duplication set when creating new `State`s
type StateUniqueSet = std::collections::HashSet<StateProcessingKey>;

/// Map for finding matching `State`s on `complete`
type StateCompletionMap<'gram> = std::collections::HashMap<StateCompletionKey<'gram>, Vec<StateId>>;

/// Arena allocator for `State`s which also manages:
/// * de-duplication of new `State`s
/// * a queue of unprocessed `State`s
/// * a map of `State`s for completion matching
#[derive(Debug, Default)]
struct StateArena<'gram> {
    arena: AppendOnlyVec<State<'gram>, StateId>,
    unprocessed: std::collections::VecDeque<StateId>,
    processed_set: StateUniqueSet,
    matching_map: StateCompletionMap<'gram>,
}

/// Unprocessed `State` fields.
/// Does not return `State` directly, for simpler lifetimes.
/// Full `State` is available via `StateArena::get` and `key`
struct Unprocessed<'gram> {
    key: StateId,
    matching: Option<&'gram Term>,
    input_range: InputRange<'gram>,
}

impl<'gram> StateArena<'gram> {
    pub fn new() -> Self {
        Self::default()
    }
    /// Allocate new `State`s
    pub fn alloc_extend(&mut self, iter: impl Iterator<Item = State<'gram>>) {
        for state in iter {
            let state_key = StateProcessingKey::from_state(&state);
            let is_new_state = self.processed_set.insert(state_key);

            if !is_new_state {
                continue;
            }

            let matching_state_key = StateCompletionKey::from_state(&state);

            let state_key = self.arena.push(state);
            self.unprocessed.push_back(state_key);

            if let Some(Term::Nonterminal(_)) = matching_state_key.term {
                self.matching_map
                    .entry(matching_state_key)
                    .or_insert_with(Vec::new)
                    .push(state_key);
            }
        }
    }
    /// Get `State` stored in arena by `ArenaKey`
    pub fn get(&self, key: StateId) -> Option<&State<'gram>> {
        self.arena.get(key)
    }
    /// Get `State`s which match for state completion
    pub fn get_matching(&self, state: &State<'gram>) -> impl Iterator<Item = &State<'gram>> {
        let key = StateCompletionKey::from_complete(state);
        self.matching_map
            .get(&key)
            .into_iter()
            .flat_map(|keys| keys.iter())
            .filter_map(|key| self.get(*key))
    }
    /// Pop next unprocessed state fields from front of queue
    pub fn pop_unprocessed(&mut self) -> Option<Unprocessed<'gram>> {
        self.unprocessed
            .pop_front()
            .and_then(|key| self.arena.get(key).map(|state| (state, key)))
            .map(|(state, key)| Unprocessed {
                key,
                input_range: state.input_range.clone(),
                matching: state.unmatched_terms.matching(),
            })
    }
}

/// Iterator for parsing input according to `Grammar`
struct ParseIter<'gram> {
    grammar: Grammar<'gram>,
    state_arena: StateArena<'gram>,
}

impl<'gram> ParseIter<'gram> {
    pub fn new(grammar: &'gram crate::Grammar, input: &'gram str) -> Self {
        let grammar = Grammar::new(grammar);

        let state_arena = StateArena::new();

        let mut parse_iter = Self {
            grammar,
            state_arena,
        };

        let starting_input_range = InputRange::new(input);
        let starting_states = parse_iter.grammar.starting_iter().map(|prod| {
            State::new(
                prod.lhs,
                prod.id.clone(),
                &prod.rhs.terms,
                starting_input_range.clone(),
            )
        });

        parse_iter.state_arena.alloc_extend(starting_states);

        parse_iter
    }
    fn get_parse_tree(&self, state: &State<'gram>) -> ParseTree<'gram> {
        let (lhs, _) = self
            .grammar
            .get_production_parts_by_id(&state.production_id);

        let rhs = state
            .matched_terms
            .iter()
            .filter_map(|child| match child {
                TermMatch::Terminal(term) => Some(ParseTreeNode::Terminal(term)),
                TermMatch::NonTerminal(key) => {
                    let state = self.state_arena.get(*key);
                    state.map(|state| ParseTreeNode::Nonterminal(self.get_parse_tree(state)))
                }
            })
            .collect();

        ParseTree::new(lhs, rhs)
    }
}

impl<'gram> Iterator for ParseIter<'gram> {
    type Item = ParseTree<'gram>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(Unprocessed {
            key,
            matching,
            input_range,
        }) = self.state_arena.pop_unprocessed()
        {
            // buffer for when new states are created
            let mut created_states = Vec::<State>::new();
            match matching {
                // predict
                Some(matching @ Term::Nonterminal(_)) => {
                    let predictions = predict(matching, &input_range, &self.grammar);
                    self.state_arena.alloc_extend(predictions);

                    let nullable_predictions =
                        predict_nullable(matching, &input_range, &self.grammar);
                    self.state_arena.alloc_extend(nullable_predictions);
                }
                // scan
                Some(Term::Terminal(_)) => {
                    let state = self.state_arena.get(key)?;
                    let scanned = scan(state);
                    created_states.extend(scanned);
                    self.state_arena.alloc_extend(created_states.drain(..));
                }
                // complete
                None => {
                    let state = self.state_arena.get(key)?;
                    if state.is_complete(&self.grammar.starting_production_ids) {
                        let parse_tree = self.get_parse_tree(state);
                        return Some(parse_tree);
                    }

                    let completed = self
                        .state_arena
                        .get_matching(state)
                        .map(|parent| complete(key, &input_range, parent));
                    created_states.extend(completed);

                    self.state_arena.alloc_extend(created_states.drain(..));
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
    ParseIter::new(grammar, input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;

    #[test]
    fn parse_dna_left_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <dna> <base>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_dna_right_recursive() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_ambiguous() {
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
    fn parse_complete_empty() {
        let grammar: Grammar = "<start> ::= \"hi\" <empty>
        <empty> ::= \"\""
            .parse()
            .unwrap();

        let input = "hi";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_empty() {
        let grammar: Grammar = "<start> ::= \"\"".parse().unwrap();

        let input = "";

        let parses = parse(&grammar, input);
        assert_eq!(parses.count(), 1);
    }

    #[test]
    fn parse_nested_empty_post() {
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

    // #[test]
    // fn parse_nested_empty_pre() {
    //     let grammar: Grammar = "
    //     <start> ::= <empty> <a>
    //     <a> ::= <empty> 'a'
    //     <empty> ::= ''"
    //         .parse()
    //         .unwrap();

    //     let input = "a";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

    // #[test]
    // fn parse_nested_empty_pre_and_post() {
    //     let grammar: Grammar = "
    //     <start> ::= <empty> <a> <empty>
    //     <a> ::= <empty> 'a' <empty>
    //     <empty> ::= ''"
    //         .parse()
    //         .unwrap();

    //     let input = "a";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

    // #[test]
    // fn parse_inline_empty() {
    //     let grammar: Grammar = "
    //     <start> ::= <a> '' <a>
    //     <a> ::= 'a'"
    //         .parse()
    //         .unwrap();

    //     let input = "aa";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

    // (source: <https://loup-vaillant.fr/tutorials/earley-parsing/empty-rules>)
    // #[test]
    // fn parse_empty_infinite() {
    //     let grammar: Grammar = "
    //     <a> ::= '' | <b>
    //     <b> ::= <a>"
    //         .parse()
    //         .unwrap();

    //     let input = "";

    //     let parses = parse(&grammar, input);
    //     assert_eq!(parses.count(), 1);
    // }

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
    fn parse_math() {
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
