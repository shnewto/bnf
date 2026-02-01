//! Grammar generation strategies.
//!
//! This module provides pluggable strategies for choosing which production
//! expression to expand during sentence generation, enabling use cases such
//! as depth-bounded generation, coverage-guided testing, and weighted fuzzing.

use crate::expression::Expression;
use crate::production::Production;
use crate::term::Term;
use rand::Rng;
use rand::SeedableRng;
use rand::rng;
use rand::rngs::StdRng;

/// Strategy for choosing which RHS alternative to use when expanding a nonterminal
/// during grammar sentence generation.
pub trait GenerationStrategy {
    /// Choose one of the production's RHS alternatives.
    ///
    /// Returns `Some(&expression)` for the chosen alternative, or `None` if
    /// there is no valid choice (e.g. depth-bounded with no terminal-only option).
    fn choose<'p>(&mut self, production: &'p Production, depth: usize) -> Option<&'p Expression>;
}

/// Uniform random choice over all expressions (current default behavior).
#[derive(Debug)]
#[non_exhaustive]
pub struct RandomWalk {
    rng: StdRng,
}

impl Default for RandomWalk {
    fn default() -> Self {
        let mut seed = [0u8; 32];
        rng().fill(&mut seed);
        Self {
            rng: StdRng::from_seed(seed),
        }
    }
}

impl RandomWalk {
    /// Create a strategy seeded from the given seed for reproducible generation.
    #[must_use]
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Self {
            rng: StdRng::from_seed(seed),
        }
    }
}

impl GenerationStrategy for RandomWalk {
    fn choose<'p>(&mut self, production: &'p Production, _depth: usize) -> Option<&'p Expression> {
        debug_assert!(!production.is_empty(), "production must not be empty");
        let idx = random_index(&mut self.rng, production.len());
        production.get_expression(idx)
    }
}

/// At or above `max_depth`, only chooses expressions that are all terminals,
/// guaranteeing termination. Below `max_depth`, behaves like [`RandomWalk`].
///
/// Suited for generating "dummy" data for a UI or database seed that is valid but strictly bounded in size.
#[derive(Debug)]
#[non_exhaustive]
pub struct DepthBounded {
    /// Maximum expansion depth; at this depth only terminal-only expressions are chosen.
    pub max_depth: usize,
    rng: StdRng,
    /// Reused buffer for eligible indices at depth; avoids per-call allocation.
    eligible_buf: Vec<usize>,
}

impl DepthBounded {
    /// Create a depth-bounded strategy with the given maximum depth.
    #[must_use]
    pub fn new(max_depth: usize) -> Self {
        let mut seed = [0u8; 32];
        rng().fill(&mut seed);
        Self {
            max_depth,
            rng: StdRng::from_seed(seed),
            eligible_buf: Vec::new(),
        }
    }

    /// Create a strategy seeded from the given seed for reproducible generation.
    #[must_use]
    pub fn from_seed(max_depth: usize, seed: [u8; 32]) -> Self {
        Self {
            max_depth,
            rng: StdRng::from_seed(seed),
            eligible_buf: Vec::new(),
        }
    }

    fn expression_all_terminals(expression: &Expression) -> bool {
        expression
            .terms_iter()
            .all(|t| matches!(t, Term::Terminal(_)))
    }

    /// Fill `eligible_buf` with indices of RHS expressions valid at the given depth, then pick one
    /// uniformly, or fallback to any index if none are eligible. Reuses `eligible_buf` to avoid alloc.
    fn fill_eligible_and_choose_index(&mut self, production: &Production, depth: usize) -> usize {
        self.eligible_buf.clear();
        if depth >= self.max_depth {
            for (i, expr) in production.rhs_iter().enumerate() {
                if Self::expression_all_terminals(expr) {
                    self.eligible_buf.push(i);
                }
            }
        } else {
            self.eligible_buf.extend(0..production.len());
        }
        if self.eligible_buf.is_empty() {
            random_index(&mut self.rng, production.len())
        } else {
            *self
                .eligible_buf
                .get(random_index(&mut self.rng, self.eligible_buf.len()))
                .expect("index in 0..eligible_buf.len()")
        }
    }
}

/// Uniform random index in `0..len`. Shared by strategies that need uniform choice.
fn random_index(rng: &mut StdRng, len: usize) -> usize {
    rng.random_range(0..len)
}

impl GenerationStrategy for DepthBounded {
    fn choose<'p>(&mut self, production: &'p Production, depth: usize) -> Option<&'p Expression> {
        debug_assert!(!production.is_empty(), "production must not be empty");
        let idx = self.fill_eligible_and_choose_index(production, depth);
        production.get_expression(idx)
    }
}

/// Prefers expressions that have not yet been exercised; tracks (nonterminal, index) coverage.
///
/// Suited for generating data that fully explores all options of the grammar.
#[derive(Debug)]
pub struct CoverageGuided {
    /// (nonterminal, `expression_index`) pairs that have been chosen.
    seen: crate::HashSet<(*const Term, usize)>,
    rng: StdRng,
    /// Reused buffer for uncovered indices; avoids per-call allocation.
    candidates_buf: Vec<usize>,
}

impl Default for CoverageGuided {
    fn default() -> Self {
        let seed = [0u8; 32];
        Self {
            seen: crate::HashSet::new(),
            rng: StdRng::from_seed(seed),
            candidates_buf: Vec::new(),
        }
    }
}

impl CoverageGuided {
    /// Create a new coverage-guided strategy with no coverage yet.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a strategy seeded from the given seed for reproducible generation.
    #[must_use]
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Self {
            seen: crate::HashSet::new(),
            rng: StdRng::from_seed(seed),
            candidates_buf: Vec::new(),
        }
    }

    /// Fill `candidates_buf` with indices not yet in `seen` for this production's LHS, then pick one
    /// uniformly, or fallback to any index if all are seen. Reuses `candidates_buf` to avoid alloc.
    fn fill_uncovered_and_choose_index(&mut self, production: &Production) -> usize {
        let lhs = &production.lhs as *const Term;
        self.candidates_buf.clear();
        for i in 0..production.len() {
            if !self.seen.contains(&(lhs, i)) {
                self.candidates_buf.push(i);
            }
        }
        if self.candidates_buf.is_empty() {
            random_index(&mut self.rng, production.len())
        } else {
            *self
                .candidates_buf
                .get(random_index(&mut self.rng, self.candidates_buf.len()))
                .expect("index in 0..candidates_buf.len()")
        }
    }
}

impl GenerationStrategy for CoverageGuided {
    fn choose<'p>(&mut self, production: &'p Production, _depth: usize) -> Option<&'p Expression> {
        debug_assert!(!production.is_empty(), "production must not be empty");
        let idx = self.fill_uncovered_and_choose_index(production);
        self.seen.insert((&production.lhs as *const Term, idx));
        production.get_expression(idx)
    }
}

/// Weights expressions by whether they contain a recursive reference to the current
/// nonterminal (higher weight for recursive, for fuzzing / stress testing).
#[derive(Debug)]
#[non_exhaustive]
pub struct Weighted {
    /// Weight for an expression that contains the current nonterminal (recursive).
    pub recursive_weight: u32,
    /// Weight for an expression that does not.
    pub non_recursive_weight: u32,
    rng: StdRng,
    /// Reused buffer for expression weights; avoids per-call allocation.
    weights_buf: Vec<u32>,
}

impl Default for Weighted {
    fn default() -> Self {
        let seed = [0u8; 32];
        Self {
            recursive_weight: 100,
            non_recursive_weight: 1,
            rng: StdRng::from_seed(seed),
            weights_buf: Vec::new(),
        }
    }
}

impl Weighted {
    /// Create a weighted strategy with custom weights.
    #[must_use]
    pub fn new(recursive_weight: u32, non_recursive_weight: u32) -> Self {
        Self {
            recursive_weight,
            non_recursive_weight,
            ..Default::default()
        }
    }

    /// Create a strategy seeded from the given seed for reproducible generation.
    #[must_use]
    pub fn from_seed(recursive_weight: u32, non_recursive_weight: u32, seed: [u8; 32]) -> Self {
        Self {
            recursive_weight,
            non_recursive_weight,
            rng: StdRng::from_seed(seed),
            weights_buf: Vec::new(),
        }
    }

    fn expression_contains_nonterminal(expression: &Expression, nonterminal: &Term) -> bool {
        expression.terms_iter().any(|t| *t == *nonterminal)
    }

    /// Fill `weights_buf` with one weight per RHS expression; reuses buffer to avoid alloc.
    fn fill_weights(&mut self, production: &Production) {
        let lhs = &production.lhs;
        self.weights_buf.clear();
        for expr in production.rhs_iter() {
            let w = if Self::expression_contains_nonterminal(expr, lhs) {
                self.recursive_weight
            } else {
                self.non_recursive_weight
            };
            self.weights_buf.push(w);
        }
    }

    /// Weighted random index; if total weight is 0, returns uniform random in `0..fallback_len`.
    fn weighted_random_index(rng: &mut StdRng, weights: &[u32], fallback_len: usize) -> usize {
        let total: u32 = weights.iter().sum();
        if total == 0 {
            return random_index(rng, fallback_len);
        }
        let mut r = rng.random_range(0..total);
        for (i, &w) in weights.iter().enumerate() {
            if r < w {
                return i;
            }
            r -= w;
        }
        weights.len().saturating_sub(1)
    }
}

impl GenerationStrategy for Weighted {
    fn choose<'p>(&mut self, production: &'p Production, _depth: usize) -> Option<&'p Expression> {
        debug_assert!(!production.is_empty(), "production must not be empty");
        self.fill_weights(production);
        let idx = Self::weighted_random_index(&mut self.rng, &self.weights_buf, production.len());
        production.get_expression(idx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::Expression;
    use crate::production::Production;
    use crate::term::Term;

    /// Production with one epsilon alternative (RHS has one expression with no terms).
    fn empty_production() -> Production {
        crate::production!(<s> ::= )
    }

    /// Production with no RHS alternatives (zero expressions).
    fn production_with_no_expressions() -> Production {
        Production::from_parts(Term::Nonterminal("s".to_string()), vec![])
    }

    #[test]
    fn random_walk_empty_production_chooses_epsilon() {
        let mut strategy = RandomWalk::default();
        let production = empty_production();
        let result = strategy.choose(&production, 0);
        assert!(result.is_some(), "single epsilon is a valid choice");
        assert!(
            result.unwrap().terms_iter().next().is_none(),
            "chosen expression is epsilon (no terms)"
        );
    }

    #[test]
    #[should_panic]
    fn random_walk_production_with_no_expressions_panics() {
        let mut strategy = RandomWalk::default();
        let production = production_with_no_expressions();
        let _ = strategy.choose(&production, 0);
    }

    #[test]
    fn depth_bounded_empty_production_chooses_epsilon() {
        let mut strategy = DepthBounded::new(5);
        let production = empty_production();
        let result = strategy.choose(&production, 0);
        assert!(result.is_some(), "single epsilon is a valid choice");
        assert!(
            result.unwrap().terms_iter().next().is_none(),
            "chosen expression is epsilon (no terms)"
        );
    }

    #[test]
    #[should_panic]
    fn depth_bounded_production_with_no_expressions_panics() {
        let mut strategy = DepthBounded::new(5);
        let production = production_with_no_expressions();
        let _ = strategy.choose(&production, 0);
    }

    #[test]
    fn depth_bounded_at_max_depth_no_terminal_only_chooses_any() {
        // At max_depth with only non-terminal expressions, indices is empty; we fall back to choosing any
        let mut strategy = DepthBounded::new(1);
        let production = Production::from_parts(
            Term::Nonterminal("s".to_string()),
            vec![Expression::from_parts(vec![
                Term::Terminal("(".to_string()),
                Term::Nonterminal("s".to_string()),
                Term::Terminal(")".to_string()),
            ])],
        );
        let result = strategy.choose(&production, 1);
        let chosen = result.expect("should choose one");
        let first = production.rhs_iter().next().expect("one alternative");
        assert!(chosen == first);
    }

    #[test]
    fn coverage_guided_empty_production_chooses_epsilon() {
        let mut strategy = CoverageGuided::new();
        let production = empty_production();
        let result = strategy.choose(&production, 0);
        assert!(result.is_some(), "single epsilon is a valid choice");
        assert!(
            result.unwrap().terms_iter().next().is_none(),
            "chosen expression is epsilon (no terms)"
        );
    }

    #[test]
    #[should_panic]
    fn coverage_guided_production_with_no_expressions_panics() {
        let mut strategy = CoverageGuided::new();
        let production = production_with_no_expressions();
        let _ = strategy.choose(&production, 0);
    }

    #[test]
    fn weighted_default_can_generate() {
        // Exercise Weighted::default() by using it in generation
        let grammar: crate::Grammar = "<s> ::= 'x' | <s> 'x'
        "
        .parse()
        .unwrap();
        let mut strategy = Weighted::default();
        let s = grammar
            .generate_seeded_with_strategy(&mut strategy)
            .expect("generate should succeed");
        assert!(!s.is_empty());
        assert!(s.chars().all(|c| c == 'x'));
    }

    #[test]
    fn weighted_total_zero_returns_any_index() {
        let mut strategy = Weighted::new(0, 0);
        let production = Production::from_parts(
            Term::Nonterminal("s".to_string()),
            vec![
                Expression::from_parts(vec![Term::Terminal("a".to_string())]),
                Expression::from_parts(vec![Term::Terminal("b".to_string())]),
            ],
        );
        let result = strategy.choose(&production, 0);
        let chosen = result.expect("should choose one");
        assert!(production.rhs_iter().any(|e| e == chosen));
    }

    #[test]
    fn weighted_loop_subtract_path() {
        // Two alternatives: first recursive (weight 1), second not (weight 10).
        let production = Production::from_parts(
            Term::Nonterminal("s".to_string()),
            vec![
                Expression::from_parts(vec![Term::Nonterminal("s".to_string())]),
                Expression::from_parts(vec![Term::Terminal("a".to_string())]),
            ],
        );
        let second = production.get_expression(1).expect("two alternatives");
        let mut seen_second = false;
        for seed in 0..100u8 {
            let mut strategy = Weighted::from_seed(1, 10, [seed; 32]);
            let choice = strategy.choose(&production, 0).unwrap();
            if choice == second {
                seen_second = true;
                break;
            }
        }
        assert!(
            seen_second,
            "weighted should sometimes choose non-recursive option"
        );
    }
}
