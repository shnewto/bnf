//! Grammar module for parsing and manipulating Backus-Naur Form (BNF) grammars.
//!
//! This module provides the core functionality for working with context-free grammars
//! defined in BNF notation. It includes support for parsing grammars from strings,
//! generating random sentences, parsing input against grammars, and displaying
//! parse trees.
//!
//! # Unicode Support
//!
//! The library fully supports Unicode throughout all operations:
//! - Unicode characters in terminal strings (e.g., `'😀'`, `'α'`, `'Hello'`)
//! - Unicode characters in nonterminal names (e.g., `<表情>`, `<emoji>`)
//! - Unicode input strings for parsing
//! - Unicode output in generated sentences and parse tree displays
//!
//! # Examples
//!
//! ```rust
//! use bnf::Grammar;
//!
//! // Basic grammar parsing
//! let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
//! <base> ::= 'A' | 'C' | 'G' | 'T'".parse().unwrap();
//!
//! // Unicode terminals
//! let grammar: Grammar = "<emoji> ::= '😀' | '😍' | '🎉'
//! <text> ::= <emoji> | <emoji> <text>".parse().unwrap();
//!
//! // Unicode nonterminals
//! let grammar: Grammar = "<表情> ::= '😀' | '😍'
//! <文本> ::= <表情> | <表情> <文本>".parse().unwrap();
//!
//! ```

#[cfg(feature = "ABNF")]
use crate::ABNF;
use crate::error::Error;
use crate::expression::Expression;
use crate::parsers::{self, BNF, Format};
use crate::production::Production;
use crate::term::Term;
use rand::{Rng, SeedableRng, rng, rngs::StdRng, seq::IndexedRandom};
use std::borrow::Cow;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use std::fmt;
use std::str;

/// A node of a `ParseTree`, either terminating or continuing the `ParseTree`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseTreeNode<'parser, 'gram> {
    Terminal(&'parser str),
    Nonterminal(ParseTree<'parser, 'gram>),
}

/// A tree derived by successfully parsing an input string via [`crate::GrammarParser::parse_input()`]
///
/// `'parser` is the lifetime of the reference (parser/grammar borrow); `'gram` is the lifetime
/// of the grammar data. This split allows using a local grammar without `Box::leak`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseTree<'parser, 'gram> {
    /// the "left hand side" `Term` used for this `ParseTree`
    pub lhs: &'parser Term<'gram>,
    rhs: Vec<ParseTreeNode<'parser, 'gram>>,
}

impl<'parser, 'gram> ParseTree<'parser, 'gram> {
    pub(crate) const fn new(
        lhs: &'parser Term<'gram>,
        rhs: Vec<ParseTreeNode<'parser, 'gram>>,
    ) -> Self {
        Self { lhs, rhs }
    }
}

// A set of column indices, used for tracking which columns are active when formatting a `ParseTree`
type ParseTreeFormatSet = std::collections::HashSet<usize>;

impl<'parser, 'gram> ParseTree<'parser, 'gram> {
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
        depth_format_set: &mut ParseTreeFormatSet,
        depth: usize,
        is_last_child: bool,
    ) -> fmt::Result {
        // set the current column index as "active"
        depth_format_set.insert(depth);

        // print the current node prefix with glyphs for active columns, e.g. "│   └── "
        Self::fmt_node_prefix(f, depth_format_set, depth, is_last_child)?;

        // print the current node in form "LHS ::= RHS1 RHS2 ..."
        write!(f, "{} ::=", self.lhs)?;

        for matched in &self.rhs {
            match matched {
                ParseTreeNode::Terminal(terminal) => write!(f, " \"{terminal}\"")?,
                ParseTreeNode::Nonterminal(parse_tree) => write!(f, " {}", parse_tree.lhs)?,
            }
        }

        writeln!(f)?;

        // recursively print children, noting which is a "last child"
        // because they receive different prefix string ("├── <base>" vs "└── <base>"")
        let child_depth = depth + 1;
        let last_child_idx = self.rhs.len() - 1;

        for (idx, child) in self.rhs.iter().enumerate() {
            let is_last_child = idx == last_child_idx;
            if is_last_child {
                depth_format_set.remove(&depth);
            }
            match child {
                ParseTreeNode::Terminal(terminal) => {
                    Self::fmt_node_prefix(f, depth_format_set, child_depth, is_last_child)?;
                    writeln!(f, "\"{terminal}\"")?;
                }
                ParseTreeNode::Nonterminal(nonterminal) => {
                    nonterminal.fmt(f, depth_format_set, child_depth, is_last_child)?;
                }
            }
        }

        Ok(())
    }

    fn fmt_node_prefix(
        f: &mut fmt::Formatter,
        depth_format_set: &mut ParseTreeFormatSet,
        depth: usize,
        is_last_child: bool,
    ) -> fmt::Result {
        const CHILD_PREFIX: &str = "├── ";
        const GRANDCHILD_PREFIX: &str = "│   ";
        const LAST_CHILD_PREFIX: &str = "└── ";
        const LAST_GRANDCHILD_PREFIX: &str = "    ";

        for idx in 0..depth {
            let prefix = if (idx + 1) == depth {
                if is_last_child {
                    LAST_CHILD_PREFIX
                } else {
                    CHILD_PREFIX
                }
            } else if depth_format_set.contains(&idx) {
                GRANDCHILD_PREFIX
            } else {
                LAST_GRANDCHILD_PREFIX
            };
            write!(f, "{prefix}")?;
        }

        Ok(())
    }

    /// Opt into formatting as [Mermaid.js](https://mermaid-js.github.io/) flowchart.
    ///
    /// ```
    /// # use bnf::Grammar;
    /// let grammar = "<dna> ::= <base> | <base> <dna>
    /// <base> ::= 'A' | 'C' | 'G' | 'T'"
    ///     .parse::<Grammar>()
    ///     .unwrap();
    /// let parser = grammar.build_parser().unwrap();
    /// let input = "GATTACA";
    /// let parses: Vec<_> = parser.parse_input(input).collect();
    /// let mermaid = parses[0].mermaid_to_string();
    /// println!("parse tree mermaid: {}", mermaid);
    /// ```
    #[must_use]
    pub const fn mermaid(&'parser self) -> MermaidParseTree<'parser, 'gram> {
        MermaidParseTree { parse_tree: self }
    }

    /// Return this parse tree as a Mermaid diagram string.
    /// Convenience method; equivalent to `self.mermaid().to_string()`.
    #[must_use]
    pub fn mermaid_to_string(&self) -> String {
        self.mermaid().to_string()
    }

    /// Iterate the "right hand side" parse tree nodes
    pub fn rhs_iter<'a>(&'a self) -> impl Iterator<Item = &'a ParseTreeNode<'parser, 'gram>> {
        self.rhs.iter()
    }

    /// Mutably iterate the "right hand side" parse tree nodes
    pub fn rhs_iter_mut<'a>(
        &'a mut self,
    ) -> impl Iterator<Item = &'a mut ParseTreeNode<'parser, 'gram>> {
        self.rhs.iter_mut()
    }
}

impl fmt::Display for ParseTree<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut depth_format_set = ParseTreeFormatSet::new();
        self.fmt(f, &mut depth_format_set, 0, true)
    }
}

/// Wrap `ParseTree` in "Mermaid" type, which opts into new implementation of `std::fmt::Display`.
/// Writes `ParseTree` as [Mermaid.js](https://mermaid-js.github.io/) flowchart.
pub struct MermaidParseTree<'parser, 'gram> {
    parse_tree: &'parser ParseTree<'parser, 'gram>,
}

impl MermaidParseTree<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, count: &mut usize) -> fmt::Result {
        if *count == 0 {
            writeln!(f, "flowchart TD")?;
        }

        // write line for each child
        // A --> B
        // A --> C
        // id1([This is the text in the box])
        let lhs = match self.parse_tree.lhs {
            Term::Nonterminal(s) => s.as_ref(),
            Term::Terminal(_) => unreachable!(),
            Term::AnonymousNonterminal(_) => unreachable!(),
        };

        let lhs_count = *count;

        for rhs in &self.parse_tree.rhs {
            *count += 1;
            match rhs {
                ParseTreeNode::Terminal(rhs) => {
                    writeln!(f, "{}[\"{}\"] --> {}[\"{}\"]", lhs_count, lhs, *count, rhs)?;
                }
                ParseTreeNode::Nonterminal(parse_tree) => {
                    let rhs = match parse_tree.lhs {
                        Term::Nonterminal(s) => s.as_ref(),
                        Term::Terminal(_) => unreachable!(),
                        Term::AnonymousNonterminal(_) => unreachable!(),
                    };
                    writeln!(f, "{}[\"{}\"] --> {}[\"{}\"]", lhs_count, lhs, *count, rhs)?;
                    let mermaid = MermaidParseTree { parse_tree };
                    mermaid.fmt(f, count)?;
                }
            };
        }

        Ok(())
    }
}

impl fmt::Display for MermaidParseTree<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut count = 0usize;
        self.fmt(f, &mut count)
    }
}

/// A Grammar is comprised of any number of Productions.
///
/// The library fully supports Unicode throughout all operations, including Unicode
/// characters in terminals, nonterminals, input strings, and generated output.
///
/// # Data lifetime and const grammars
///
/// Grammar uses [`Cow`] internally: runtime parsing (e.g. [`Grammar::parse_from`],
/// [`FromStr`](std::str::FromStr)) yields `Grammar<'static>` with `Cow::Owned` data. To build a grammar
/// at compile time with no runtime allocation, use `Cow::Borrowed` and const data:
/// define const [`Term`]s, const arrays of terms, then
/// [`Expression::from_borrowed`](crate::Expression::from_borrowed), then
/// [`Production::from_borrowed_rhs`](crate::Production::from_borrowed_rhs), then
/// [`Grammar::from_borrowed`]. See the `const_grammar` example.
#[derive(Clone, Default, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct Grammar<'a> {
    productions: Cow<'a, [Production<'a>]>,
}

impl<'a> Grammar<'a> {
    /// Construct a new `Grammar`
    #[must_use]
    pub const fn new() -> Grammar<'a> {
        Grammar {
            productions: Cow::Owned(vec![]),
        }
    }

    /// Construct an `Grammar` from `Production`s
    #[must_use]
    pub const fn from_parts(v: Vec<Production<'a>>) -> Grammar<'a> {
        Grammar {
            productions: Cow::Owned(v),
        }
    }

    /// Construct a `Grammar` from a borrowed slice of productions.
    /// Use this for const grammars with `Cow::Borrowed` data; runtime parsing yields
    /// `Grammar<'static>` with `Cow::Owned`.
    #[must_use]
    pub const fn from_borrowed(productions: &'a [Production<'a>]) -> Grammar<'a> {
        Grammar {
            productions: Cow::Borrowed(productions),
        }
    }

    /// parse a grammar given a format
    pub fn parse_from<F: Format>(input: &str) -> Result<Grammar<'static>, self::Error> {
        match parsers::grammar_complete::<F>(input) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }

    /// Add `Production` to the `Grammar`
    pub fn add_production(&mut self, prod: Production<'a>) {
        self.productions.to_mut().push(prod);
    }

    /// Remove `Production` from the `Grammar`
    pub fn remove_production(&mut self, prod: &Production<'a>) -> Option<Production<'a>> {
        let prods = self.productions.to_mut();
        prods
            .iter()
            .position(|x| *x == *prod)
            .map(|pos| prods.remove(pos))
    }

    /// Get iterator of the `Grammar`'s `Production`s
    pub fn productions_iter(&self) -> impl Iterator<Item = &Production<'a>> {
        self.productions.iter()
    }

    /// Get mutable iterator of the `Grammar`'s `Production`s
    pub fn productions_iter_mut(&mut self) -> impl Iterator<Item = &mut Production<'a>> {
        self.productions.to_mut().iter_mut()
    }

    /// Build a reusable parser from this grammar, validating that all nonterminals are defined.
    ///
    /// This method validates the grammar and creates a [`crate::GrammarParser`] that can be
    /// reused to parse multiple input strings efficiently.
    ///
    /// # Errors
    ///
    /// Returns `Error::ValidationError` if any nonterminal used in the RHS of
    /// productions lacks a definition in the grammar, or if the grammar has no productions.
    ///
    /// # Example
    ///
    /// ```rust
    /// use bnf::Grammar;
    ///
    /// let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
    /// <base> ::= 'A' | 'C' | 'G' | 'T'"
    ///     .parse()
    ///     .unwrap();
    ///
    /// let parser = grammar.build_parser().unwrap();
    /// let parse_trees: Vec<_> = parser.parse_input("GATTACA").collect();
    /// ```
    ///
    /// The parser holds a reference to this grammar for lifetime `'b`; the grammar's data
    /// may live longer (`'a`). This allows using a local grammar without `Box::leak`.
    pub fn build_parser<'b>(&'b self) -> Result<crate::GrammarParser<'b, 'a>, Error>
    where
        'a: 'b,
    {
        crate::GrammarParser::new(self)
    }

    /// Get the starting term
    pub(crate) fn starting_term(&self) -> Option<&Term<'a>> {
        self.productions_iter().next().map(|prod| &prod.lhs)
    }

    fn eval_terminal(
        &self,
        term: &Term<'a>,
        rng: &mut StdRng,
        f: &impl Fn(&str, &str) -> bool,
    ) -> Result<String, Error> {
        match term {
            Term::Nonterminal(nt) => self.traverse(nt.as_ref(), rng, f),
            Term::Terminal(t) => Ok(t.to_string()),
            Term::AnonymousNonterminal(rhs) => {
                let Some(expression) = rhs.choose(rng) else {
                    return Err(Error::GenerateError(String::from(
                        "Couldn't select random Expression!",
                    )));
                };

                let mut result = String::new();
                for term in expression.terms_iter() {
                    match self.eval_terminal(term, rng, f) {
                        Ok(s) => result.push_str(&s),
                        Err(e) => return Err(e),
                    }
                }
                Ok(result)
            }
        }
    }

    fn traverse(
        &self,
        ident: &str,
        rng: &mut StdRng,
        f: &impl Fn(&str, &str) -> bool,
    ) -> Result<String, Error> {
        loop {
            let find_lhs = self.productions_iter().find(|x| match &x.lhs {
                Term::Nonterminal(nt) => nt.as_ref() == ident,
                _ => false,
            });

            let Some(production) = find_lhs else {
                return Ok(ident.to_string());
            };

            let expressions = production.rhs_iter().collect::<Vec<&Expression>>();

            let Some(expression) = expressions.choose(rng) else {
                return Err(Error::GenerateError(String::from(
                    "Couldn't select random Expression!",
                )));
            };

            let mut result = String::new();
            for term in expression.terms_iter() {
                match self.eval_terminal(term, rng, f) {
                    Ok(s) => result.push_str(&s),
                    Err(e) => return Err(e),
                }
            }

            if f(ident, &result) {
                return Ok(result);
            }
        }
    }

    /// Generate a random sentence from self and seed for random.
    /// Use if interested in reproducing the output generated.
    /// Begins from lhs of first production.
    ///
    /// # Random Number Generation
    ///
    /// This method uses the provided RNG for random number generation. The cryptographic
    /// security of the generated sentences depends entirely on the RNG implementation
    /// provided by the caller. For cryptographically secure generation, use a secure
    /// RNG like `StdRng` from the `rand` crate. For deterministic output for testing
    /// or reproducibility, use any seedable RNG with a fixed seed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use bnf::rand::{SeedableRng, rngs::StdRng};
    /// use bnf::Grammar;
    ///
    /// let input =
    ///     "<dna> ::= <base> | <base> <dna>
    ///     <base> ::= 'A' | 'C' | 'G' | 'T'";
    /// let grammar: Grammar = input.parse().unwrap();
    /// let seed: [u8; 32] = [0; 32];
    /// let mut rng: StdRng = SeedableRng::from_seed(seed);
    /// let sentence = grammar.generate_seeded(&mut rng);
    /// # let sentence_clone = sentence.clone();
    /// match sentence {
    ///     Ok(s) => println!("random sentence: {}", s),
    ///     Err(e) => println!("something went wrong: {}!", e)
    /// }
    ///
    /// # assert!(sentence_clone.is_ok());
    /// ```
    pub fn generate_seeded(&self, rng: &mut StdRng) -> Result<String, Error> {
        self.generate_seeded_callback(rng, |_, _| true)
    }

    /// Does the same as [`Grammar::generate_seeded`], except it takes a callback which is
    /// executed on every production that is generated to check if it is okay.
    /// When the callback returns `true`, the generation continues as normal,
    /// but when the callback returns `false`, a new random option is tried.
    ///
    /// # Random Number Generation
    ///
    /// This method uses the provided RNG for random number generation. The cryptographic
    /// security of the generated sentences depends entirely on the RNG implementation
    /// provided by the caller. For cryptographically secure generation, use a secure
    /// RNG like `StdRng` from the `rand` crate. For deterministic output for testing
    /// or reproducibility, use any seedable RNG with a fixed seed.
    ///
    /// The first parameter to the callback is the current production name,
    /// and the second parameter is the value that was attempted to be
    /// generated, but may be rejected.
    pub fn generate_seeded_callback(
        &self,
        rng: &mut StdRng,
        f: impl Fn(&str, &str) -> bool,
    ) -> Result<String, Error> {
        let start_rule: String;
        let first_production = self.productions_iter().next();

        if !self.terminates() {
            return Err(Error::GenerateError(
                "Can't generate, first rule in grammar doesn't lead to a terminal state"
                    .to_string(),
            ));
        }

        match first_production {
            Some(term) => match &term.lhs {
                Term::Nonterminal(nt) => start_rule = nt.to_string(),
                Term::Terminal(_) => {
                    return Err(Error::GenerateError(format!(
                        "Terminal type cannot define a production in '{term}'!"
                    )));
                }
                Term::AnonymousNonterminal(_) => unreachable!(),
            },
            None => {
                return Err(Error::GenerateError(String::from(
                    "Failed to get first production!",
                )));
            }
        }
        self.traverse(&start_rule, rng, &f)
    }

    /// Generate a random sentence from self.
    /// Begins from lhs of first production.
    ///
    /// # Example
    ///
    /// ```rust
    /// use bnf::Grammar;
    ///
    /// let input =
    ///     "<dna> ::= <base> | <base> <dna>
    ///     <base> ::= 'A' | 'C' | 'G' | 'T'";
    /// let grammar: Grammar = input.parse().unwrap();
    /// let sentence = grammar.generate();
    /// # let sentence_clone = sentence.clone();
    /// match sentence {
    ///     Ok(s) => println!("random sentence: {}", s),
    ///     Err(e) => println!("something went wrong: {}!", e)
    /// }
    ///
    /// # assert!(sentence_clone.is_ok());
    /// ```
    pub fn generate(&self) -> Result<String, Error> {
        self.generate_callback(|_, _| true)
    }

    /// Does the same as [`Grammar::generate`], except it takes a callback which is
    /// executed on every production that is generated to check if it is okay.
    /// When the callback returns `true`, the generation continues as normal,
    /// but when the callback returns `false`, a new random option is tried.
    ///
    /// # Random Number Generation
    ///
    /// This method uses the system's default random number generator. The cryptographic
    /// security of the generated sentences depends on the system's RNG implementation.
    /// For applications requiring cryptographically secure generation, consider using
    /// [`Grammar::generate_seeded_callback`] with a secure RNG like `StdRng` from the `rand` crate.
    ///
    /// The first parameter to the callback is the current production name,
    /// and the second parameter is the value that was attempted to be
    /// generated, but may be rejected.
    pub fn generate_callback(&self, f: impl Fn(&str, &str) -> bool) -> Result<String, Error> {
        // let seed: &[_] = &[1, 2, 3, 4];
        let mut seed: [u8; 32] = [0; 32];
        rng().fill(&mut seed);
        let mut rng: StdRng = SeedableRng::from_seed(seed);
        self.generate_seeded_callback(&mut rng, f)
    }

    /// Determine if the starting rule of the grammar can take us to a terminal state, i.e. all
    /// [`Term::Terminal`] types. Used as a check before generation, to tell if we can safely attempt
    /// to generate sentences without risking infinite loops
    pub(crate) fn terminates(&self) -> bool {
        let Some(starting_term) = self.starting_term() else {
            // if there are no rules, there's nothing to do so... it terminates
            return true;
        };

        let mut terminating_rules: Vec<&Term> = vec![];

        // collect 'every non-terminal that produces a sequences of terminals'
        for p in self.productions.iter() {
            if p.has_terminating_expression(None) {
                terminating_rules.push(&p.lhs);
            }
        }

        if terminating_rules.is_empty() {
            return false;
        }

        let mut is_progress = true;

        while is_progress {
            is_progress = false;

            for prod in self.productions_iter() {
                let marked = terminating_rules.contains(&&prod.lhs);

                // if already marked, then no need to reprocess
                if marked {
                    continue;
                }

                let terminates = prod.has_terminating_expression(Some(&terminating_rules));

                if terminates {
                    // only care if the starting term terminates, so can return early
                    if &prod.lhs == starting_term {
                        return true;
                    }

                    terminating_rules.push(&prod.lhs);
                    is_progress = true;
                }
            }
        }

        terminating_rules.contains(&starting_term)
    }
}

impl<'a> fmt::Display for Grammar<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "{}",
            self.productions
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl str::FromStr for Grammar<'static> {
    type Err = Error;
    #[cfg(feature = "ABNF")]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        //try and autodetect the format (in the feature we'll use a detector that returns an enum, hence the gratuitous switch case)
        match parsers::is_format_standard_bnf(s) {
            true => match parsers::grammar_complete::<BNF>(s) {
                Result::Ok((_, o)) => Ok(o),
                Result::Err(e) => Err(Error::from(e)),
            },
            false => match parsers::grammar_complete::<ABNF>(s) {
                Result::Ok((_, o)) => Ok(o),
                Result::Err(e) => Err(Error::from(e)),
            },
        }
    }
    #[cfg(not(feature = "ABNF"))]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parsers::grammar_complete::<BNF>(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use super::*;
    use crate::expression::Expression;
    use crate::production::Production;
    use crate::term::Term;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    impl Arbitrary for Grammar<'static> {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut productions = Vec::<Production<'static>>::arbitrary(g);
            // grammar must always have atleast one production
            if productions.is_empty() {
                productions.push(Production::arbitrary(g));
            }
            Grammar {
                productions: Cow::Owned(productions),
            }
        }
    }

    fn prop_to_string_and_back(gram: Grammar<'static>) -> TestResult {
        let to_string = gram.to_string();
        let from_str: Result<Grammar, _> = to_string.parse();
        match from_str {
            Ok(from_prod) => TestResult::from_bool(from_prod == gram),
            _ => TestResult::error(format!("{gram} to string and back should be safe")),
        }
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new()
            .tests(1000)
            .r#gen(Gen::new(12usize))
            .quickcheck(prop_to_string_and_back as fn(Grammar<'static>) -> TestResult);
    }

    #[test]
    fn new_grammars() {
        let lhs1 = Term::Nonterminal(Cow::Owned(String::from("STRING A")));
        let rhs1 = Expression::from_parts(vec![
            Term::Terminal(Cow::Owned(String::from("STRING B"))),
            Term::Nonterminal(Cow::Owned(String::from("STRING C"))),
        ]);
        let p1 = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2 = Term::Nonterminal(Cow::Owned(String::from("STRING A")));
        let rhs2 = Expression::from_parts(vec![
            Term::Terminal(Cow::Owned(String::from("STRING B"))),
            Term::Nonterminal(Cow::Owned(String::from("STRING C"))),
        ]);
        let p2 = Production::from_parts(lhs2, vec![rhs2]);

        let mut g1 = Grammar::new();
        g1.add_production(p1.clone());
        g1.add_production(p2.clone());
        let g2 = Grammar::from_parts(vec![p1, p2]);
        assert_eq!(g1, g2);
    }

    #[test]
    fn add_production() {
        let production = crate::production!(<dna> ::= "base" | "base" <dna>);
        let productions = vec![production.clone()];
        let mut grammar = Grammar::new();

        // grammar starts empty
        assert_eq!(grammar.productions_iter().count(), 0);

        grammar.add_production(production);

        // grammar now has production
        assert_eq!(grammar.productions_iter().count(), 1);

        // mutated grammar identical to new grammar built from same productions
        let filled_grammar = Grammar::from_parts(productions);
        assert_eq!(grammar, filled_grammar);
    }

    #[test]
    fn remove_production() {
        let production = crate::production!(<dna> ::= "base" | "base" <dna>);
        let productions = vec![production.clone()];
        let mut grammar = Grammar::from_parts(productions.clone());

        // grammar has production
        assert_eq!(
            Some(&production),
            grammar.productions_iter().find(|&prod| *prod == production)
        );
        assert_eq!(grammar.productions_iter().count(), productions.len());

        // production has been removed
        let removed = grammar.remove_production(&production);
        assert_eq!(removed, Some(production.clone()));
        assert_eq!(grammar.productions_iter().count(), productions.len() - 1);
        assert_eq!(
            None,
            grammar.productions_iter().find(|&prod| *prod == production)
        );
    }

    #[test]
    fn remove_nonexistent_production() {
        let production = crate::production!(<dna> ::= "base" | "base" <dna>);
        let productions = vec![production.clone()];
        let mut grammar = Grammar::from_parts(productions.clone());

        let unused = crate::production!(<nonexistent> ::=);

        // grammar has original production
        assert_eq!(
            Some(&production),
            grammar.productions_iter().find(|&prod| *prod == production)
        );
        assert_eq!(grammar.productions_iter().count(), productions.len());

        // unused production is not removed
        let removed = grammar.remove_production(&unused);
        assert_eq!(removed, None);
        assert_eq!(grammar.productions_iter().count(), productions.len());
        assert_eq!(
            None,
            grammar.productions_iter().find(|&prod| *prod == unused)
        );
    }

    #[test]
    fn parse_error() {
        let grammar: Result<Grammar, _> = "<almost_grammar> ::= <test".parse();
        assert!(grammar.is_err(), "{grammar:?} should be error");
    }

    #[test]
    fn parse_error_on_incomplete() {
        let result: Result<Grammar, _> = "".parse();
        assert!(
            matches!(result, Err(Error::ParseError(_))),
            "{result:?} should be ParseError"
        );
    }

    #[test]
    fn parse_from_bnf_format() {
        use crate::parsers::BNF;
        let input = "<dna> ::= <base> | <base> <dna>\n<base> ::= 'A' | 'C' | 'G' | 'T'";
        let result = Grammar::parse_from::<BNF>(input);
        assert!(result.is_ok(), "Should parse BNF format");
        let grammar = result.unwrap();
        assert!(grammar.productions_iter().count() >= 2);
    }

    #[cfg(feature = "ABNF")]
    #[test]
    fn parse_from_abnf_format() {
        use crate::parsers::ABNF;
        let input = "dna = base / base dna\nbase = \"A\" / \"C\" / \"G\" / \"T\"";
        let result = Grammar::parse_from::<ABNF>(input);
        assert!(result.is_ok(), "Should parse ABNF format");
        let grammar = result.unwrap();
        assert!(grammar.productions_iter().count() >= 2);
    }

    #[test]
    fn parse_from_error() {
        use crate::parsers::BNF;
        let input = "<incomplete";
        let result = Grammar::parse_from::<BNF>(input);
        assert!(result.is_err(), "Should fail on incomplete input");
        assert!(matches!(result.unwrap_err(), Error::ParseError(_)));
    }

    #[test]
    fn generate_with_empty_anonymous_nonterminal() {
        // Test error path when AnonymousNonterminal has empty expressions
        let empty_anon = Term::AnonymousNonterminal(Cow::Owned(vec![]));
        let production = Production::from_parts(
            crate::term!(<start>),
            vec![Expression::from_parts(vec![empty_anon])],
        );
        let grammar = Grammar::from_parts(vec![production]);
        let result = grammar.generate();
        assert!(
            result.is_err(),
            "Should fail when AnonymousNonterminal is empty"
        );
        if let Err(Error::GenerateError(msg)) = result {
            assert!(msg.contains("Couldn't select random Expression"));
        } else {
            panic!("Expected GenerateError");
        }
    }

    #[test]
    fn lhs_is_terminal_parse() {
        let grammar: Result<Grammar, _> = "\"wrong place\" ::= <not-used>".parse();
        assert!(grammar.is_err(), "{grammar:?} should be error");
    }

    #[test]
    fn lhs_is_terminal_generate() {
        let lhs = Term::Terminal(Cow::Owned(String::from("\"bad LHS\"")));
        let terminal = Term::Terminal(Cow::Owned(String::from("\"good RHS\"")));
        let expression = Expression::from_parts(vec![terminal]);
        let production = Production::from_parts(lhs, vec![expression]);
        let grammar = Grammar::from_parts(vec![production]);
        let sentence = grammar.generate();
        assert!(sentence.is_err(), "{sentence:?} should be error");
    }

    #[test]
    fn no_productions() {
        let grammar = Grammar::from_parts(vec![]);
        let sentence = grammar.generate();
        assert!(sentence.is_err(), "{sentence:?} should be error");
    }

    #[test]
    fn no_expressions() {
        let lhs = Term::Terminal(Cow::Owned(String::from("<good-lhs>")));
        let production = Production::from_parts(lhs, vec![]);
        let grammar = Grammar::from_parts(vec![production]);
        let sentence = grammar.generate();
        assert!(sentence.is_err(), "{sentence:?} should be error");
    }

    #[test]
    fn format_grammar() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();
        let format = format!("{grammar}");
        assert_eq!(
            format,
            "<dna> ::= <base> | <base> <dna>\n<base> ::= 'A' | 'C' | 'G' | 'T'\n"
        );
    }

    #[test]
    fn iterate_parse_tree() {
        let grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse::<Grammar>()
            .unwrap();

        let input = "GATTACA";

        let parse_tree = grammar
            .build_parser()
            .unwrap()
            .parse_input(input)
            .next()
            .unwrap();

        let rhs_iterated = parse_tree.rhs_iter().next().unwrap();

        assert_eq!(parse_tree.rhs.first().unwrap(), rhs_iterated);
    }

    #[test]
    fn iterate_mut_parse_tree() {
        let grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse::<Grammar>()
            .unwrap();

        let input = "GATTACA";

        let mut parse_tree = grammar
            .build_parser()
            .unwrap()
            .parse_input(input)
            .next()
            .unwrap();

        let rhs_iterated = parse_tree.rhs_iter_mut().next().unwrap();

        *rhs_iterated = ParseTreeNode::Terminal("Z");

        assert_eq!(
            parse_tree.rhs.first().unwrap(),
            &ParseTreeNode::Terminal("Z")
        );
    }

    #[test]
    fn does_not_terminate() {
        let mut grammar: Grammar = "<nonterm> ::= <nonterm>".parse().unwrap();
        assert!(!grammar.terminates());

        grammar = "
        <A> ::= <X> | <A> <X>
        <X> ::= <Y> | <X> <Y>
        <Y> ::= <Y> <Z>
        <Z> ::= 'terminating state!'"
            .parse()
            .unwrap();
        assert!(!grammar.terminates());

        grammar = "
        <not-a-good-first-state-lhs> ::= <not-a-good-first-state-rhs>
        <A> ::= <X> | <A> <X>
        <X> ::= <Y> | <X> <Y>
        <Y> ::= <Z> | <Y> <Z>
        <Z> ::= 'terminating state!'"
            .parse()
            .unwrap();
        assert!(!grammar.terminates());
    }

    #[test]
    fn does_terminate() {
        let mut grammar: Grammar;
        grammar = "<nonterm> ::= 'term'".parse().unwrap();
        assert!(grammar.terminates());

        grammar = "
        <A> ::= <B> | <A> <B>
        <B> ::= <C> | <B> <C>
        <C> ::= <D> | <C> <D>
        <D> ::= <E> | <D> <E>
        <E> ::= <F> | <E> <F>
        <F> ::= <G> | <F> <G>
        <G> ::= <H> | <G> <H>
        <H> ::= <I> | <H> <I>
        <I> ::= <J> | <I> <J>
        <J> ::= <K> | <J> <K>
        <K> ::= <L> | <K> <L>
        <L> ::= <M> | <L> <M>
        <M> ::= <N> | <M> <N>
        <N> ::= <O> | <N> <O>
        <O> ::= <P> | <O> <P>
        <P> ::= <Q> | <P> <Q>
        <Q> ::= <R> | <Q> <R>
        <R> ::= <S> | <R> <S>
        <S> ::= <T> | <S> <T>
        <T> ::= <U> | <T> <U>
        <U> ::= <V> | <U> <V>
        <V> ::= <W> | <V> <W>
        <W> ::= <X> | <W> <X>
        <X> ::= <Y> | <X> <Y>
        <Y> ::= <Z> | <Y> <Z>
        <Z> ::= 'terminating state!'"
            .parse()
            .unwrap();
        assert!(grammar.terminates());
    }
    // <dna> ::= <base> | <base> <dna>;

    /// Tests grammar construction via string parsing (not the grammar! macro).
    #[test]
    fn parse_construct() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>; <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();
        let expected: Grammar = "<dna> ::= <base> | <base> <dna>; <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();
        assert_eq!(grammar, expected);
    }

    // Unicode support tests
    #[test]
    fn unicode_grammar_parsing() {
        // Test parsing a grammar with Unicode characters in terminals
        let grammar: Result<Grammar, _> = "<emoji> ::= '😀' | '😍' | '🎉' | '🚀'
        <symbol> ::= 'α' | 'β' | 'γ' | 'δ'
        <text> ::= <emoji> | <symbol> | <emoji> <text>"
            .parse();

        assert!(grammar.is_ok(), "Should parse Unicode grammar: {grammar:?}");

        let grammar = grammar.unwrap();
        assert_eq!(grammar.productions_iter().count(), 3);
    }

    #[test]
    fn unicode_grammar_generation() {
        // Test generating sentences from Unicode grammar
        let grammar: Grammar = "<emoji> ::= '😀' | '😍' | '🎉' | '🚀'
        <symbol> ::= 'α' | 'β' | 'γ' | 'δ'
        <text> ::= <emoji> | <symbol> | <emoji> <text>"
            .parse()
            .unwrap();

        let sentence = grammar.generate();
        assert!(
            sentence.is_ok(),
            "Should generate Unicode sentence: {sentence:?}"
        );

        let sentence = sentence.unwrap();
        // The generated sentence should contain Unicode characters
        assert!(
            sentence.contains('😀')
                || sentence.contains('😍')
                || sentence.contains('🎉')
                || sentence.contains('🚀')
                || sentence.contains('α')
                || sentence.contains('β')
                || sentence.contains('γ')
                || sentence.contains('δ')
        );
    }

    #[test]
    fn unicode_input_parsing() {
        // Test parsing Unicode input against a grammar
        let grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse::<Grammar>()
            .unwrap();

        let input = "😀🎉";
        let parser = grammar.build_parser().unwrap();
        let mut parse_trees = parser.parse_input(input);

        assert!(
            parse_trees.next().is_some(),
            "Should parse Unicode input '{input}'"
        );
    }

    #[test]
    fn unicode_parse_tree_display() {
        // Test that parse trees with Unicode display correctly
        let grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse::<Grammar>()
            .unwrap();

        let input = "😀😍";
        let parse_tree = grammar
            .build_parser()
            .unwrap()
            .parse_input(input)
            .next()
            .unwrap();

        let display = parse_tree.to_string();

        // Should contain Unicode characters in the parse tree display
        assert!(display.contains('😀') || display.contains('😍'));
    }

    #[test]
    fn unicode_parse_tree_iteration() {
        // Test that parse trees with Unicode can be iterated
        let grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse::<Grammar>()
            .unwrap();

        let input = "😀😍🎉";
        let parse_tree = grammar
            .build_parser()
            .unwrap()
            .parse_input(input)
            .next()
            .unwrap();

        // Test iteration over RHS nodes
        let rhs_count = parse_tree.rhs_iter().count();
        assert!(rhs_count > 0, "Should have RHS nodes in Unicode parse tree");

        // Test mutable iteration
        let mut parse_tree_clone = parse_tree.clone();
        let mut rhs_iter = parse_tree_clone.rhs_iter_mut();
        assert!(
            rhs_iter.next().is_some(),
            "Should be able to iterate mutably over Unicode parse tree"
        );
    }

    #[test]
    fn unicode_mermaid_format() {
        // Test that Unicode parse trees can be formatted as Mermaid
        let grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse::<Grammar>()
            .unwrap();

        let input = "😀😍";
        let parse_tree = grammar
            .build_parser()
            .unwrap()
            .parse_input(input)
            .next()
            .unwrap();

        let mermaid = parse_tree.mermaid().to_string();

        // Mermaid output should contain the flowchart structure
        assert!(
            mermaid.contains("flowchart TD"),
            "Mermaid should contain flowchart declaration"
        );
        assert!(
            mermaid.contains("-->"),
            "Mermaid should contain connection arrows"
        );
    }

    #[test]
    fn unicode_complex_grammar() {
        // Test a more complex Unicode grammar with multiple productions
        let grammar: Grammar = "<greeting> ::= 'Hello' | 'Hola' | 'Bonjour' | '😀'
        <name> ::= 'Alice' | 'Bob' | 'Charlie' | 'αβγ'
        <punctuation> ::= '.' | '!' | '?' | '🎉'
        <sentence> ::= <greeting> <name> <punctuation> | <greeting> <sentence>"
            .parse()
            .unwrap();

        let sentence = grammar.generate();
        assert!(
            sentence.is_ok(),
            "Should generate from complex Unicode grammar: {sentence:?}"
        );

        let sentence = sentence.unwrap();
        // Should contain various types of Unicode content
        assert!(
            sentence.contains("Hello")
                || sentence.contains("Hola")
                || sentence.contains("Bonjour")
                || sentence.contains('😀')
                || sentence.contains("Alice")
                || sentence.contains("Bob")
                || sentence.contains("Charlie")
                || sentence.contains("αβγ")
                || sentence.contains('.')
                || sentence.contains('!')
                || sentence.contains('?')
                || sentence.contains('🎉')
        );
    }

    #[test]
    fn unicode_nonterminal_names() {
        // Test that nonterminal names can contain Unicode characters
        let grammar = "<文本> ::= <表情> | <符号> | <表情> <文本>
        <表情> ::= '😀' | '😍'
        <符号> ::= 'α' | 'β'"
            .parse::<Grammar>()
            .unwrap();

        let sentence = grammar.generate();
        assert!(
            sentence.is_ok(),
            "Should generate from grammar with Unicode nonterminals: {sentence:?}"
        );

        let sentence = sentence.unwrap();
        // Should contain Unicode characters from the terminals
        assert!(
            sentence.contains('😀')
                || sentence.contains('😍')
                || sentence.contains('α')
                || sentence.contains('β')
        );

        // Test parsing input with this grammar
        let input = "😀α";
        let parser = grammar.build_parser().unwrap();
        let mut parse_trees = parser.parse_input(input);
        assert!(
            parse_trees.next().is_some(),
            "Should parse Unicode input with Unicode nonterminals: '{input}'"
        );
    }

    #[test]
    fn parse_starting_with() {
        let grammar = "<base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>"
            .parse::<Grammar>()
            .unwrap();

        let input = "GATTACA";
        let dna_term = crate::term!(<dna>);
        let base_term = crate::term!(<base>);
        let parser = grammar.build_parser().unwrap();

        assert!(
            parser
                .parse_input_starting_with(input, &dna_term)
                .next()
                .is_some()
        );
        assert!(
            parser
                .parse_input_starting_with(input, &base_term)
                .next()
                .is_none()
        );
    }

    #[test]
    fn parse_starting_with_not_found_production() {
        let grammar = "<base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>"
            .parse::<Grammar>()
            .unwrap();

        let input = "GATTACA";
        let notfound = crate::term!(<notfound>);
        assert!(
            grammar
                .build_parser()
                .unwrap()
                .parse_input_starting_with(input, &notfound)
                .next()
                .is_none()
        )
    }
}
