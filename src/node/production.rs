use std::fmt;
use std::slice;
use node::Expression;
use node::Term;


#[derive(PartialEq, Debug, Clone)]
/// A Production is comprised of any number of Expressions
pub struct Production {
    pub lhs: Term,
    rhs: Vec<Expression>,
}

impl Production {
    /// Construct a new `Production`
    pub fn new() -> Production {
        Production {
            lhs: Term::Nonterminal(String::new()),
            rhs: vec![],
        }
    }

    /// Construct an `Production` from `Expression`s
    pub fn from_parts(t: Term, e: Vec<Expression>) -> Production {
        Production { lhs: t, rhs: e }
    }

    /// Add `Expression` to the `Production`'s right hand side
    pub fn add_to_rhs(&mut self, expr: Expression) {
        self.rhs.push(expr)
    }

    /// Remove `Expression` from the `Production`'s right hand side
    ///
    /// If interested if `Expression` was removed, then inspect the returned `Option`.
    pub fn remove_from_rhs(&mut self, expr: &Expression) -> Option<Expression> {
        if let Some(pos) = self.rhs.iter().position(|x| *x == *expr) {
            Some(self.rhs.remove(pos))
        } else {
            None
        }
    }

    /// Get iterator of the `Production`'s right hand side `Expression`s
    pub fn rhs_iter(&self) -> Iter {
        Iter {
            iterator: self.rhs.iter(),
        }
    }

    /// Get iterator of the `Production`'s right hand side `Expression`s
    pub fn rhs_iter_mut(&mut self) -> IterMut {
        IterMut {
            iterator: self.rhs.iter_mut(),
        }
    }
}

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ::= {}",
            self.lhs.to_string(),
            self.rhs
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(" | ")
        )
    }
}

pub struct Iter<'a> {
    iterator: slice::Iter<'a, Expression>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Expression;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}

pub struct IterMut<'a> {
    iterator: slice::IterMut<'a, Expression>,
}

impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Expression;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_productions() {
        let lhs1: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs1: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p1: Production = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2: Term = Term::Nonterminal(String::from("STRING A"));
        let rhs2: Expression = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let mut p2: Production = Production::new();
        p2.lhs = lhs2;
        p2.add_to_rhs(rhs2);

        assert_eq!(p1, p2);
    }

    #[test]
    fn remove_from_rhs() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        // unnecessary expression to be removed from production
        let two_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more, two_more.clone()];
        let mut production = Production::from_parts(lhs, expression_list.clone());
        let removed = production.remove_from_rhs(&two_more);

        // the removed element should be the accident
        assert_eq!(Some(two_more.clone()), removed);
        // number of productions should have decreased
        assert_eq!(production.rhs_iter().count(), expression_list.len() - 1);
        // the unnecessary should no longer be found
        assert_eq!(
            production
                .rhs_iter()
                .find(|&expression| *expression == two_more),
            None
        );
    }

    #[test]
    fn remove_nonexistent_from_rhs() {
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let mut production = Production::from_parts(lhs, expression_list.clone());

        // unused expression to fail being removed from production
        let two_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let removed = production.remove_from_rhs(&two_more);

        // the unused term should not be found in the terms
        assert_eq!(production.rhs_iter().find(|&expr| *expr == two_more), None);
        // no term should have been removed
        assert_eq!(None, removed);
        // number of terms should not have decreased
        assert_eq!(production.rhs_iter().count(), expression_list.len());
    }
}
