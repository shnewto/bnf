use crate::append_vec::{append_only_vec_id, AppendOnlyVec};

append_only_vec_id!(pub(crate) ProductionId);
append_only_vec_id!(pub(crate) MatchingProductionId);

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
    id: ProductionId,
    lhs: &'gram crate::Term,
    rhs: &'gram crate::Expression,
}

#[derive(Debug)]
pub(crate) struct MatchingProduction<'gram> {
    prod_id: ProductionId,
    matching: Vec<MatchingTerm<'gram>>,
}

type ProdTermMap<'gram> = std::collections::HashMap<&'gram crate::Term, Vec<ProductionId>>;
type NullProdTermMap<'gram> =
    std::collections::HashMap<&'gram crate::Term, Vec<MatchingProductionId>>;

#[derive(Debug)]
pub(crate) struct MatchingGrammar<'gram> {
    starting_production_ids: Vec<ProductionId>,
    productions: AppendOnlyVec<Production<'gram>, ProductionId>,
    prods_by_lhs: ProdTermMap<'gram>,
    prods_by_rhs: ProdTermMap<'gram>,
    matching_productions: AppendOnlyVec<MatchingProduction<'gram>, MatchingProductionId>,
    null_matches_by_lhs: NullProdTermMap<'gram>,
}
