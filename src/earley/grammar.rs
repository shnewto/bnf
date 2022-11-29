use crate::append_vec::{append_only_vec_id, AppendOnlyVec};
use crate::tracing;
use std::rc::Rc;

append_only_vec_id!(pub(crate) ProductionId);

/// A [`crate::Term`] which has been "matched" while parsing input
#[derive(Debug, Clone)]
pub(crate) enum TermMatch<'gram> {
    /// [`crate::Term::Terminal`] which matched with a string literal
    Terminal(&'gram str),
    /// [`crate::Term::Nonterminal`] which was matched with a fully completed production
    Nonterminal(Rc<ProductionMatch<'gram>>),
}

/// A `Term` to be "matched" with input
#[derive(Debug, Clone)]
pub(crate) enum TermMatching<'gram> {
    /// A [`crate::Term`] which has not yet been matched
    Unmatched(&'gram crate::Term),
    /// A [`crate::Term`] which has been matched
    Matched(TermMatch<'gram>),
}

/// [`crate::Production`] offers multiple possible "right hand side" [`crate::Expression`]s, which is overly flexible for Earley parsing.
/// [`Production`] is a one-to-one relationship of [`crate::Term`] -> [`crate::Expression`].
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

/// An attempt at matching a [`Production`]'s "right hand side" [`crate::Term`]s
#[derive(Debug, Clone)]
pub(crate) struct ProductionMatching<'gram> {
    pub prod_id: ProductionId,
    pub lhs: &'gram crate::Term,
    /// "right hand side" [`TermMatching`]s which are partitioned by the matched and unmatched.
    /// For example: [Matched, Matched, Matched, Unmatched, Unmatched]
    rhs: Vec<TermMatching<'gram>>,
    /// The progress cursor used to separate [`TermMatching`]s in the "right hand side"
    matched_count: usize,
}

impl<'gram> ProductionMatching<'gram> {
    /// Attempt to "complete" the production, by having no unmatched terms remaining.
    pub fn complete(&self) -> Option<ProductionMatch<'gram>> {
        let rhs: Option<Vec<TermMatch>> = self
            .rhs
            .iter()
            .map(|term| match term {
                TermMatching::Unmatched(_) => None,
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
                lhs: self.lhs,
                rhs,
                input_len,
            }
        })
    }
    /// Get the next unmatched [`crate::Term`]
    pub fn next(&self) -> Option<&'gram crate::Term> {
        self.rhs.get(self.matched_count).map(|term| match term {
            TermMatching::Matched(_) => {
                unreachable!("terms ahead of matching cursor cannot already be matched")
            }
            TermMatching::Unmatched(term) => *term,
        })
    }
    /// Get how many [`crate::Term`] have been matched
    pub fn matched_count(&self) -> usize {
        self.matched_count
    }
    /// Add a [`TermMatch`].
    /// Does **not** check if the added term is a valid match. That responsibility is on the caller,
    /// which likely has more context for faster matching of terms.
    pub fn add_term_match(&self, term_match: TermMatch<'gram>) -> Option<Self> {
        // only match term if there is next
        self.next().map(|_| {
            let Self {
                lhs,
                matched_count,
                rhs,
                prod_id,
            } = self;
            let prod_id = *prod_id;

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

/// A fully complete [`ProductionMatching`].
/// Created via [`ProductionMatching::complete`]
#[derive(Debug, Clone)]
pub(crate) struct ProductionMatch<'gram> {
    pub lhs: &'gram crate::Term,
    pub rhs: Vec<TermMatch<'gram>>,
    pub input_len: usize,
}

type ProdArena<'gram> = AppendOnlyVec<Production<'gram>, ProductionId>;
type ProdTermMap<'gram> = std::collections::HashMap<&'gram crate::Term, Vec<ProductionId>>;
type NullMatchMap<'gram> =
    std::collections::HashMap<&'gram crate::Term, Vec<Rc<ProductionMatch<'gram>>>>;

/// Similar to [`crate::Grammar`], but using [`Production`] and tables useful for parsing.
#[derive(Debug)]
pub(crate) struct GrammarMatching<'gram> {
    starting_production_ids: Vec<ProductionId>,
    productions: ProdArena<'gram>,
    prods_by_lhs: ProdTermMap<'gram>,
    null_matches_by_lhs: NullMatchMap<'gram>,
}

impl<'gram, 'a> GrammarMatching<'gram> {
    pub fn new(grammar: &'gram crate::Grammar) -> Self {
        let _span = tracing::span!(tracing::Level::TRACE, "GrammarMatching::new").entered();
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
            let prod = productions.push_with_id(|id| Production { id, lhs, rhs });
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

        let null_matches_by_lhs = NullMatchMap::new();

        let mut grammar = Self {
            prods_by_lhs,
            null_matches_by_lhs,
            productions,
            starting_production_ids,
        };

        grammar.find_null_matches();

        grammar
    }
    // TODO: test if "nullable" rules come first
    fn find_null_matches(&mut self) {
        let mut null_matchings: Vec<ProductionMatching> = self
            .productions
            .iter()
            .map(|prod| prod.start_matching())
            .collect();

        while let Some(null_match) = null_matchings.pop() {
            match null_match.next() {
                None => self
                    .null_matches_by_lhs
                    .entry(null_match.lhs)
                    .or_default()
                    .push(Rc::new(null_match.complete().unwrap())),
                Some(unmatched_term) => match unmatched_term {
                    crate::Term::Terminal(terminal) => {
                        if terminal.is_empty() {
                            let new_null_match =
                                null_match.add_term_match(TermMatch::Terminal("")).unwrap();
                            null_matchings.push(new_null_match);
                        }
                    }
                    crate::Term::Nonterminal(_) => {
                        if let Some(null_term_prod) = self.null_matches_by_lhs.get(&unmatched_term)
                        {
                            let new_null_match = null_term_prod.iter().map(|rhs_match| {
                                null_match
                                    .add_term_match(TermMatch::Nonterminal(rhs_match.clone()))
                                    .unwrap()
                            });
                            null_matchings.extend(new_null_match);
                        }
                    }
                },
            };
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
    ) -> impl Iterator<Item = &Rc<ProductionMatch<'gram>>> {
        self.null_matches_by_lhs.get(lhs).into_iter().flatten()
    }
    pub fn is_starting_prod_id(&self, id: &ProductionId) -> bool {
        self.starting_production_ids.contains(id)
    }
}
