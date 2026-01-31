use crate::append_vec::{AppendOnlyVec, append_only_vec_id};
use crate::{Term, tracing};

append_only_vec_id!(pub(crate) ProductionId);

/// [`crate::Production`] offers multiple possible "right hand side" [`crate::Expression`]s, which is overly flexible for Earley parsing.
/// [`Production`] is a one-to-one relationship of [`crate::Term`] -> [`crate::Expression`].
#[derive(Debug)]
pub(crate) struct Production<'parser, 'gram> {
    pub id: ProductionId,
    pub lhs: &'parser crate::Term<'gram>,
    pub rhs: &'parser crate::Expression<'gram>,
}

type ProdArena<'parser, 'gram> = AppendOnlyVec<Production<'parser, 'gram>, ProductionId>;
type ProdTermMap<'parser, 'gram> = crate::HashMap<&'parser crate::Term<'gram>, Vec<ProductionId>>;

/// Similar to [`crate::Grammar`], but using [`Production`] and tables useful for parsing.
#[derive(Debug)]
pub(crate) struct ParseGrammar<'parser, 'gram> {
    productions: ProdArena<'parser, 'gram>,
    prods_by_lhs: ProdTermMap<'parser, 'gram>,
}

impl<'parser, 'gram, 'a> ParseGrammar<'parser, 'gram> {
    pub fn new(grammar: &'parser crate::grammar::Grammar<'gram>) -> Self
    where
        'gram: 'parser,
    {
        let _span = tracing::span!(tracing::Level::DEBUG, "ParseGrammar_new").entered();

        let mut productions = AppendOnlyVec::<Production, ProductionId>::new();
        let mut prods_by_lhs = ProdTermMap::new();

        let flat_prod_iter = grammar
            .productions_iter()
            .flat_map(|prod| prod.rhs_iter().map(|rhs| (&prod.lhs, rhs)));

        for (lhs, rhs) in flat_prod_iter {
            let prod = productions.push_with_id(|id| Production { id, lhs, rhs });
            let id = prod.id;
            prods_by_lhs.entry(lhs).or_default().push(id);

            for term in prod.rhs.terms_iter() {
                if let Term::AnonymousNonterminal(exprs) = term {
                    for rhs in exprs.iter() {
                        let id = productions
                            .push_with_id(|id| Production { id, lhs: term, rhs })
                            .id;
                        prods_by_lhs.entry(term).or_default().push(id);
                    }
                }
            }
        }
        Self {
            prods_by_lhs,
            productions,
        }
    }
    pub fn get_production_by_id(&'a self, prod_id: ProductionId) -> &'a Production<'parser, 'gram> {
        self.productions.get(prod_id).expect("valid production ID")
    }
    /// Returns a `&'parser Term<'gram>` key from an owned/cloned term for map lookups in the two-lifetime setup.
    /// Does a linear scan over LHS keys (O(n) in number of productions).
    pub fn get_term_ref(&self, term: &crate::Term<'gram>) -> Option<&'parser crate::Term<'gram>> {
        self.prods_by_lhs.keys().find(|k| **k == term).copied()
    }

    pub fn get_productions_by_lhs(
        &self,
        lhs: &'parser crate::Term<'gram>,
    ) -> impl Iterator<Item = &Production<'parser, 'gram>> + use<'_, 'parser, 'gram> {
        self.prods_by_lhs
            .get(lhs)
            .into_iter()
            .flatten()
            .map(|prod_id| self.get_production_by_id(*prod_id))
    }
    #[cfg(test)]
    pub fn productions_iter(
        &self,
    ) -> impl Iterator<Item = &Production<'parser, 'gram>> + use<'_, 'parser, 'gram> {
        self.productions.iter()
    }
}
