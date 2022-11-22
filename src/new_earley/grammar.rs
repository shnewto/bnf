use crate::append_vec::{append_only_vec_id, AppendOnlyVec};
use std::collections::VecDeque;

append_only_vec_id!(pub(crate) ProductionId);

#[derive(Debug, Clone)]
pub(crate) enum TermMatch<'gram> {
    Terminal(&'gram str),
    Nonterminal(ProductionMatch<'gram>),
}

#[derive(Debug, Clone)]
pub(crate) enum TermMatching<'gram> {
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
    pub fn start_matching(&self) -> ProductionMatching<'gram> {
        let prod_id = self.id;
        let lhs = self.lhs;
        let rhs = self.rhs.terms_iter().map(TermMatching::Unmatched).collect();
        ProductionMatching {
            prod_id,
            lhs,
            rhs,
            matched_count: 0,
        }
    }
}

#[derive(Debug)]
pub(crate) struct ProductionMatching<'gram> {
    pub prod_id: ProductionId,
    pub lhs: &'gram crate::Term,
    rhs: Vec<TermMatching<'gram>>,
    matched_count: usize,
}

impl<'gram> ProductionMatching<'gram> {
    pub fn complete(&self) -> Option<ProductionMatch<'gram>> {
        let rhs: Option<Vec<TermMatch>> = self
            .rhs
            .iter()
            .map(|term| match term {
                TermMatching::Unmatched(_) => None,
                // TODO: avoid clone
                TermMatching::Matched(term) => Some(term.clone()),
            })
            .collect();

        rhs.map(|rhs| {
            let input_len = rhs
                .iter()
                .map(|term| match term {
                    TermMatch::Terminal(term) => term.len(),
                    TermMatch::Nonterminal(prod) => prod.input_len,
                })
                .sum();

            ProductionMatch {
                prod_id: self.prod_id,
                lhs: self.lhs,
                rhs,
                input_len,
            }
        })
    }
    pub fn next(&self) -> Option<&'gram crate::Term> {
        self.rhs.get(self.matched_count).map(|term| match term {
            TermMatching::Matched(_) => {
                unreachable!("terms ahead of matching cursor cannot already be matched")
            }
            TermMatching::Unmatched(term) => *term,
        })
    }
    pub fn matched_count(&self) -> usize {
        self.matched_count
    }
    pub fn match_term(&self, term_match: TermMatch<'gram>) -> Option<Self> {
        // only match term if there is next
        self.next().map(|_| {
            let Self {
                lhs,
                matched_count,
                rhs,
                prod_id,
            } = self;
            let prod_id = prod_id.clone();

            // TODO: avoid clone
            let mut rhs = rhs.clone();
            rhs[*matched_count] = TermMatching::Matched(term_match);
            let matched_count = matched_count + 1;

            Self {
                lhs,
                matched_count,
                prod_id,
                rhs,
            }
        })
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ProductionMatch<'gram> {
    pub prod_id: ProductionId,
    pub lhs: &'gram crate::Term,
    pub rhs: Vec<TermMatch<'gram>>,
    pub input_len: usize,
}

impl<'gram> ProductionMatch<'gram> {}

type ProdArena<'gram> = AppendOnlyVec<Production<'gram>, ProductionId>;
type ProdTermMap<'gram> = std::collections::HashMap<&'gram crate::Term, Vec<ProductionId>>;
type NullMatchMap<'gram> =
    std::collections::HashMap<&'gram crate::Term, Vec<ProductionMatch<'gram>>>;

#[derive(Debug)]
pub(crate) struct GrammarMatching<'gram> {
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
    let mut queue = VecDeque::<ProductionId>::new();

    // TODO NEXT

    null_matches_by_prod
}

impl<'gram, 'a> GrammarMatching<'gram> {
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
    pub fn get_production_by_id(&'a self, prod_id: ProductionId) -> Option<&'a Production<'gram>> {
        self.productions.get(prod_id)
    }
    pub fn get_productions_by_lhs(
        &self,
        lhs: &'gram crate::Term,
    ) -> impl Iterator<Item = &Production<'gram>> {
        self.prods_by_lhs
            .get(lhs)
            .into_iter()
            .flatten()
            .filter_map(|prod_id| self.get_production_by_id(*prod_id))
    }
    pub fn get_nullable_production_matches_by_lhs(
        &self,
        lhs: &'gram crate::Term,
    ) -> impl Iterator<Item = &ProductionMatch<'gram>> {
        self.null_matches_by_prod.get(lhs).into_iter().flatten()
    }
}
