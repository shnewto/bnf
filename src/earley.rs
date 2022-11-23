use crate::{
    append_vec::{append_only_vec_id, AppendOnlyVec},
    grammar::{ParseTree, ParseTreeNode},
    Term,
};

append_only_vec_id!(ProductionId);
append_only_vec_id!(StateId);

/// `crate::Production` offers multiple possible "right hand side" `Expression`s, which is overly flexible for Earley parsing.
/// `earley::Production` is a one-to-one relationship of `Term` -> `Expression`.
#[derive(Debug)]
struct Production<'gram> {
    id: ProductionId,
    lhs: &'gram Term,
    rhs: &'gram crate::Expression,
}

type ProdIdMap<'gram> = std::collections::HashMap<&'gram Term, Vec<ProductionId>>;
type NullMatchesMap<'gram> = std::collections::HashMap<ProductionId, Vec<Vec<TermMatch<'gram>>>>;
/// `Production`s organized to be queried during parsing.
/// Not to be confused with `crate::Grammar`.
struct Grammar<'gram> {
    starting_production_ids: Vec<ProductionId>,
    productions: AppendOnlyVec<Production<'gram>, ProductionId>,
    ids_by_lhs: ProdIdMap<'gram>,
    ids_by_rhs: ProdIdMap<'gram>,
    null_matches_by_id: NullMatchesMap<'gram>,
    // null_matches: AppendOnlyVec<TermMatch<'gram>, ()>,
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
        let mut ids_by_lhs = ProdIdMap::new();
        let mut ids_by_rhs = ProdIdMap::new();

        let flat_prod_iter = grammar
            .productions_iter()
            .flat_map(|prod| prod.rhs_iter().map(|rhs| (&prod.lhs, rhs)));

        for (lhs, rhs) in flat_prod_iter {
            let prod = productions.push_with_id(|id| {
                let prod = Production { id, lhs, rhs };
                prod
            });
            let id = prod.id;

            ids_by_lhs.entry(lhs).or_default().push(id);

            for rhs in rhs.terms_iter() {
                ids_by_rhs.entry(rhs).or_default().push(id);
            }
        }

        let starting_production_ids = ids_by_lhs
            .get(starting_term)
            .expect("starting Term has no production")
            .clone();

        let null_matches_by_id =
            Self::match_nullable_productions(&productions, &ids_by_lhs, &ids_by_rhs);

        Self {
            ids_by_lhs,
            ids_by_rhs,
            null_matches_by_id,
            productions,
            starting_production_ids,
        }
    }
    fn match_nullable_productions(
        productions: &AppendOnlyVec<Production<'gram>, ProductionId>,
        ids_by_lhs: &ProdIdMap<'gram>,
        ids_by_rhs: &ProdIdMap<'gram>,
    ) -> NullMatchesMap<'gram> {
        let mut null_matches_by_id = NullMatchesMap::new();
        let mut queue = std::collections::VecDeque::<ProductionId>::new();

        let mut match_null_production = |prod: &Production| -> Option<&Vec<ProductionId>> {
            let mut nullable_terms_match: Vec<Vec<TermMatch>> =
                vec![Vec::new(); prod.rhs.terms.len()];
            let term_match_iter = nullable_terms_match.iter_mut();
            let rhs_term_iter = prod.rhs.terms_iter();

            for (rhs_term_matched, rhs_term) in term_match_iter.zip(rhs_term_iter) {
                match rhs_term {
                    Term::Terminal(rhs_terminal) => {
                        if rhs_terminal.is_empty() {
                            *rhs_term_matched = vec![TermMatch::Terminal("")];
                        }
                    }
                    Term::Nonterminal(_) => {
                        let null_matches: Vec<TermMatch> = ids_by_lhs
                            .get(rhs_term)
                            .into_iter()
                            .flatten()
                            .filter(|term_prod_id| null_matches_by_id.contains_key(term_prod_id))
                            .map(|prod_id| TermMatch::NullableNonTerminal(*prod_id))
                            .collect();

                        if !null_matches.is_empty() {
                            *rhs_term_matched = null_matches
                        }
                    }
                };

                // if rhs term went unmatched then all rhs cannot be matched
                if rhs_term_matched.is_empty() {
                    break;
                }
            }

            // success!
            if nullable_terms_match.iter().all(|terms| !terms.is_empty()) {
                null_matches_by_id.insert(prod.id, nullable_terms_match);
                ids_by_rhs.get(prod.lhs)
            } else {
                None
            }
        };

        for prod in productions.iter() {
            if let Some(affected_prod_ids) = match_null_production(prod) {
                queue.extend(affected_prod_ids);
            }
        }

        while let Some(prod_id) = queue.pop_front() {
            let prod = productions.get(prod_id).expect("invalid production ID");

            if let Some(affected_prod_ids) = match_null_production(prod) {
                queue.extend(affected_prod_ids);
            }
        }

        null_matches_by_id
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
        self.ids_by_lhs
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

/// A matched `Term` which has been partially accepted
#[derive(Debug, Clone, Copy)]
enum TermMatch<'gram> {
    /// The `Term` matched with a terminal string
    Terminal(&'gram str),
    /// The `Term` matched with completed non-terminal `State`
    NonTerminal(StateId),
    /// TODO
    NullableNonTerminal(ProductionId),
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
    parent: &'a State<'gram>,
    grammar: &'a Grammar<'gram>,
) -> impl Iterator<Item = State<'gram>> + 'a {
    grammar
        .ids_by_lhs
        .get(matching)
        .into_iter()
        .flatten()
        .filter(|prod_id| grammar.null_matches_by_id.contains_key(prod_id))
        .map(|prod_id| {
            let term_match = TermMatch::NullableNonTerminal(*prod_id);
            let input_range_step = 0;
            State::new_term_match(parent, term_match, input_range_step)
        })
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
/// Then "<dna> ::= • <base>" is *completed* by "<base> ::= 'A' •",
/// which yields a new state: "<dna> ::= <base> •"
///
/// Note: An `State` can only be completed by another `State` with matching `StateStart`, the offset where the state is matching.
/// This has been omitted from this example, but must be respected in real parsing.
fn complete<'gram, 'a>(
    state_id: StateId,
    input_range: &'a InputRange<'gram>,
    parent: &'a State<'gram>,
) -> State<'gram> {
    let term_match = TermMatch::NonTerminal(state_id);
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
/// Full `State` is available via `StateArena::get` and `state_id`
struct Unprocessed<'gram> {
    state_id: StateId,
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
    pub fn get(&self, id: StateId) -> Option<&State<'gram>> {
        self.arena.get(id)
    }
    /// Get `State`s which match for state completion
    pub fn get_matching(&self, state: &State<'gram>) -> impl Iterator<Item = &State<'gram>> {
        let key = StateCompletionKey::from_complete(state);
        self.matching_map
            .get(&key)
            .into_iter()
            .flat_map(|state_ids| state_ids.iter())
            .filter_map(|id| self.get(*id))
    }
    /// Pop next unprocessed state fields from front of queue
    pub fn pop_unprocessed(&mut self) -> Option<Unprocessed<'gram>> {
        self.unprocessed
            .pop_front()
            .and_then(|state_id| self.arena.get(state_id).map(|state| (state, state_id)))
            .map(|(state, state_id)| Unprocessed {
                state_id,
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
                TermMatch::NonTerminal(state_id) => {
                    let state = self.state_arena.get(*state_id);
                    state.map(|state| ParseTreeNode::Nonterminal(self.get_parse_tree(state)))
                }
                TermMatch::NullableNonTerminal(prod_id) => {
                    // TODO NEXT: oh, but WHICH nullable prod rule was used?
                    // MAYBE "NullMatch" is not actually a TermMatch (altho similar)
                    // and MAYBE "matches" should also be AppendVec?
                    // can AppendVec give slices of multiple inserts? avoid Vec<T> everywhere...
                    let foo = self
                        .grammar
                        .null_matches_by_id
                        .get(prod_id)
                        .expect("invalid production ID");
                    Some(ParseTreeNode::Terminal("NULLABLE TODO"))
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
            state_id,
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

                    let state = self.state_arena.get(state_id)?;
                    let nullable_predictions = predict_nullable(matching, state, &self.grammar);
                    created_states.extend(nullable_predictions);
                    self.state_arena.alloc_extend(created_states.drain(..));
                }
                // scan
                Some(Term::Terminal(_)) => {
                    let state = self.state_arena.get(state_id)?;

                    let scanned = scan(state);
                    created_states.extend(scanned);
                    self.state_arena.alloc_extend(created_states.drain(..));
                }
                // complete
                None => {
                    let state = self.state_arena.get(state_id)?;
                    if state.is_complete(&self.grammar.starting_production_ids) {
                        let parse_tree = self.get_parse_tree(state);
                        return Some(parse_tree);
                    }

                    let completed = self
                        .state_arena
                        .get_matching(state)
                        .map(|parent| complete(state_id, &input_range, parent));
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

    // TODO: test case for <start> ::= <a> | <b>, with both <a> and <b> nullable should give two parses
    // TODO: test case for <nonterm> without a rule
    // TODO: property test which inserts empty rule terms and should still parse

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
