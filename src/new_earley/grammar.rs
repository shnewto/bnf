use crate::append_vec::{append_only_vec_id, AppendOnlyVec};

append_only_vec_id!(pub(crate) ProductionId);

#[derive(Debug)]
pub(crate) enum TermMatch<'gram> {
    Terminal(&'gram str),
    Nonterminal(Vec<TermMatch<'gram>>),
}

#[derive(Debug)]
pub(crate) enum MatchingTerm<'gram> {
    Unmatched(&'gram crate::Term),
    Matched(TermMatch<'gram>),
}

/// `crate::Production` offers multiple possible "right hand side" `Expression`s, which is overly flexible for Earley parsing.
/// `earley::Production` is a one-to-one relationship of `Term` -> `Expression`.
#[derive(Debug)]
pub(crate) struct Production<'gram> {
    pub id: ProductionId,
    pub lhs: &'gram crate::Term,
    rhs: &'gram crate::Expression,
}

impl<'gram> Production<'gram> {
    pub fn start_matching(&self) -> MatchingProduction<'gram> {
        let prod_id = self.id;
        let matching = self.rhs.terms_iter().map(MatchingTerm::Unmatched).collect();
        MatchingProduction {
            prod_id,
            matching,
            matching_idx: 0,
        }
    }
}

#[derive(Debug)]
pub(crate) struct MatchingProduction<'gram> {
    pub(crate) prod_id: ProductionId,
    matching: Vec<MatchingTerm<'gram>>,
    matching_idx: usize,
}

impl<'gram> MatchingProduction<'gram> {
    pub fn unmatched(&self) -> &[MatchingTerm] {
        &self.matching[self.matching_idx..]
    }
    pub fn matching(&self) -> Option<&MatchingTerm<'gram>> {
        self.matching.get(self.matching_idx)
    }
}

type ProdArena<'gram> = AppendOnlyVec<Production<'gram>, ProductionId>;
type ProdTermMap<'gram> = std::collections::HashMap<&'gram crate::Term, Vec<ProductionId>>;
type NullMatchMap<'gram> = std::collections::HashMap<ProductionId, Vec<MatchingProduction<'gram>>>;

#[derive(Debug)]
pub(crate) struct MatchingGrammar<'gram> {
    starting_production_ids: Vec<ProductionId>,
    productions: ProdArena<'gram>,
    prods_by_lhs: ProdTermMap<'gram>,
    prods_by_rhs: ProdTermMap<'gram>,
    null_matches_by_prod: NullMatchMap<'gram>,
}

fn find_null_matches<'gram>(
    productions: &ProdArena<'gram>,
    prods_by_lhs: &ProdTermMap<'gram>,
    prods_by_rhs: &ProdTermMap<'gram>,
) -> NullMatchMap<'gram> {
    let mut null_matches_by_prod = NullMatchMap::new();

    // TODO

    null_matches_by_prod
}

impl<'gram> MatchingGrammar<'gram> {
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
        let starting_term = &grammar
            .productions_iter()
            .next()
            .expect("Grammar must have one production to parse")
            .lhs;

        let mut productions = AppendOnlyVec::<Production, ProductionId>::new();
        let mut prods_by_lhs = ProdTermMap::new();
        let mut prods_by_rhs = ProdTermMap::new();

        let flat_prod_iter = grammar
            .productions_iter()
            .flat_map(|prod| prod.rhs_iter().map(|rhs| (&prod.lhs, rhs)));

        for (lhs, rhs) in flat_prod_iter {
            let prod = productions.push_with_id(|id| {
                let prod = Production { id, lhs, rhs };
                prod
            });
            let id = prod.id;

            prods_by_lhs.entry(lhs).or_default().push(id);

            for rhs in rhs.terms_iter() {
                prods_by_rhs.entry(rhs).or_default().push(id);
            }
        }

        let starting_production_ids = prods_by_lhs
            .get(starting_term)
            .expect("starting Term has no production")
            .clone();

        let null_matches_by_prod = find_null_matches(&productions, &prods_by_lhs, &prods_by_rhs);

        Self {
            prods_by_lhs,
            prods_by_rhs,
            null_matches_by_prod,
            productions,
            starting_production_ids,
        }
    }
    pub fn starting_productions(&self) -> impl Iterator<Item = &Production<'gram>> {
        self.starting_production_ids
            .iter()
            .filter_map(|prod_id| self.productions.get(*prod_id))
    }
}
