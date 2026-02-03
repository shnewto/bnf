//! Shared logic for collecting LHS (defined) and RHS (referenced) nonterminals
//! and iterating over undefined ones.

/// Records nonterminals that appear as LHS (defined) or RHS (referenced) in
/// productions; supports iterating over undefined nonterminals (referenced − defined).
#[derive(Debug, Default)]
pub(crate) struct NonterminalSets<'a> {
    defined: crate::HashSet<&'a str>,
    referenced: crate::HashSet<&'a str>,
}

impl<'a> NonterminalSets<'a> {
    pub(crate) fn new() -> Self {
        Self {
            defined: crate::HashSet::new(),
            referenced: crate::HashSet::new(),
        }
    }

    pub(crate) fn record_lhs(&mut self, nt: &'a str) {
        self.defined.insert(nt);
    }

    pub(crate) fn record_rhs(&mut self, nt: &'a str) {
        self.referenced.insert(nt);
    }

    /// Reserve capacity to avoid reallocations during recording.
    pub(crate) fn reserve(&mut self, defined: usize, referenced: usize) {
        self.defined.reserve(defined);
        self.referenced.reserve(referenced);
    }

    /// Iterator over nonterminals that are referenced but not defined.
    pub(crate) fn undefined(&self) -> impl Iterator<Item = &'a str> + '_ {
        self.referenced.difference(&self.defined).copied()
    }
}
