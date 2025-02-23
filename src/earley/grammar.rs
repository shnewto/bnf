use crate::append_vec::{AppendOnlyVec, append_only_vec_id};
use crate::{Term, tracing};

append_only_vec_id!(pub(crate) ProductionId);

/// [`crate::Production`] offers multiple possible "right hand side" [`crate::Expression`]s, which is overly flexible for Earley parsing.
/// [`Production`] is a one-to-one relationship of [`crate::Term`] -> [`crate::Expression`].
#[derive(Debug)]
pub(crate) struct Production<'gram> {
    pub id: ProductionId,
    pub lhs: &'gram crate::Term,
    pub rhs: &'gram crate::Expression,
}

type ProdArena<'gram> = AppendOnlyVec<Production<'gram>, ProductionId>;
type ProdTermMap<'gram> = crate::HashMap<&'gram crate::Term, Vec<ProductionId>>;

/// Similar to [`crate::Grammar`], but using [`Production`] and tables useful for parsing.
#[derive(Debug)]
pub(crate) struct ParseGrammar<'gram> {
    productions: ProdArena<'gram>,
    prods_by_lhs: ProdTermMap<'gram>,
}

impl<'gram, 'a> ParseGrammar<'gram> {
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
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
                    for rhs in exprs {
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
    pub fn get_production_by_id(&'a self, prod_id: ProductionId) -> &'a Production<'gram> {
        self.productions.get(prod_id).expect("valid production ID")
    }
    pub fn get_productions_by_lhs(
        &self,
        lhs: &'gram crate::Term,
    ) -> impl Iterator<Item = &Production<'gram>> + use<'_, 'gram> {
        self.prods_by_lhs
            .get(lhs)
            .into_iter()
            .flatten()
            .map(|prod_id| self.get_production_by_id(*prod_id))
    }
    #[cfg(test)]
    pub fn productions_iter(&self) -> impl Iterator<Item = &Production<'gram>> + use<'_, 'gram> {
        self.productions.iter()
    }
}
