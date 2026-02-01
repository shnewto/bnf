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

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use std::fmt::{self, Write};
use std::rc::Rc;
use std::str;

/// A node of a `ParseTree`, either terminating or continuing the `ParseTree`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseTreeNode<'gram> {
    Terminal(&'gram str),
    Nonterminal(ParseTree<'gram>),
}

/// A tree derived by successfully parsing an input string via [`crate::GrammarParser::parse_input()`]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseTree<'gram> {
    /// the "left hand side" `Term` used for this `ParseTree`
    pub lhs: &'gram Term,
    rhs: Vec<ParseTreeNode<'gram>>,
}

impl<'gram> ParseTree<'gram> {
    pub(crate) const fn new(lhs: &'gram Term, rhs: Vec<ParseTreeNode<'gram>>) -> Self {
        Self { lhs, rhs }
    }
}

// A set of column indices, used for tracking which columns are active when formatting a `ParseTree`
type ParseTreeFormatSet = crate::HashSet<usize>;

impl<'gram> ParseTree<'gram> {
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

        // Recursively print children, noting which is a "last child" (different prefix).
        // Skip when rhs is empty to avoid underflow; the type allows empty rhs.
        let child_depth = depth + 1;
        if let Some(last_child_idx) = self.rhs.len().checked_sub(1) {
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
    /// let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
    /// <base> ::= 'A' | 'C' | 'G' | 'T'"
    /// .parse()
    /// .unwrap();
    ///
    /// let parser = grammar.build_parser().unwrap();
    /// let input = "GATTACA";
    /// let parsed = parser.parse_input(input).next().unwrap();
    /// let mermaid = parsed.mermaid().to_string();
    /// println!("parse tree mermaid: {}", mermaid);
    /// ```
    #[must_use]
    pub const fn mermaid(&self) -> MermaidParseTree<'_> {
        MermaidParseTree { parse_tree: self }
    }

    /// Iterate the "right hand side" parse tree nodes
    pub fn rhs_iter<'a>(&'a self) -> impl Iterator<Item = &'a ParseTreeNode<'gram>> {
        self.rhs.iter()
    }

    /// Mutably iterate the "right hand side" parse tree nodes
    pub fn rhs_iter_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut ParseTreeNode<'gram>> {
        self.rhs.iter_mut()
    }
}

impl fmt::Display for ParseTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut depth_format_set = ParseTreeFormatSet::new();
        self.fmt(f, &mut depth_format_set, 0, true)
    }
}

/// Characters that must be escaped in Mermaid flowchart node labels (entity code = decimal codepoint).
/// See [Mermaid entity codes](https://mermaid.js.org/syntax/flowchart.html#entity-codes-to-escape-characters).
const MERMAID_ESCAPE_CHARS: &[char] = &['"', '&', '#', '<', '>', '[', '\\', ']', ';', '\n', '\r'];

/// Escapes a label string for use inside Mermaid flowchart node `["label"]` syntax.
/// Uses [Mermaid entity codes](https://mermaid.js.org/syntax/flowchart.html#entity-codes-to-escape-characters):
/// each special character is replaced by `#<codepoint>;` (e.g. `"` → `#34;`). Other characters are left unchanged.
#[must_use]
pub fn escape_mermaid_label(s: &str) -> String {
    let mut out = String::with_capacity(s.len().saturating_mul(2));
    for c in s.chars() {
        if MERMAID_ESCAPE_CHARS.contains(&c) {
            write!(out, "#{};", c as u32).expect("write to String never fails");
        } else {
            out.push(c);
        }
    }
    out
}

/// Wrap `ParseTree` in "Mermaid" type, which opts into new implementation of `std::fmt::Display`.
/// Writes `ParseTree` as [Mermaid.js](https://mermaid-js.github.io/) flowchart.
/// Node labels are escaped with [entity codes](https://mermaid.js.org/syntax/flowchart.html#entity-codes-to-escape-characters)
/// so that quotes, ampersand, angle brackets, brackets, backslash, hash, semicolon, and newlines render correctly.
pub struct MermaidParseTree<'a> {
    parse_tree: &'a ParseTree<'a>,
}

impl MermaidParseTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, count: &mut usize) -> fmt::Result {
        if *count == 0 {
            writeln!(f, "flowchart TD")?;
        }

        // Parser-built trees have LHS as Nonterminal; Terminal/AnonymousNonterminal are unreachable.
        let lhs = match self.parse_tree.lhs {
            Term::Nonterminal(str) => str,
            Term::Terminal(_) => unreachable!(),
        };
        let lhs_escaped = escape_mermaid_label(lhs);
        let lhs_count = *count;

        for rhs in &self.parse_tree.rhs {
            *count += 1;
            match rhs {
                ParseTreeNode::Terminal(rhs) => {
                    let rhs_escaped = escape_mermaid_label(rhs);
                    writeln!(
                        f,
                        "{}[\"{}\"] --> {}[\"{}\"]",
                        lhs_count, lhs_escaped, *count, rhs_escaped
                    )?;
                }
                ParseTreeNode::Nonterminal(parse_tree) => {
                    let rhs = match parse_tree.lhs {
                        Term::Nonterminal(str) => str,
                        Term::Terminal(_) => unreachable!(),
                    };
                    let rhs_escaped = escape_mermaid_label(rhs);
                    writeln!(
                        f,
                        "{}[\"{}\"] --> {}[\"{}\"]",
                        lhs_count, lhs_escaped, *count, rhs_escaped
                    )?;
                    let mermaid = MermaidParseTree { parse_tree };
                    mermaid.fmt(f, count)?;
                }
            };
        }

        Ok(())
    }
}

impl fmt::Display for MermaidParseTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut count = 0usize;
        self.fmt(f, &mut count)
    }
}

/// A Grammar is comprised of any number of Productions.
///
/// When parsing from text (e.g. [`str::parse`] or [`Grammar::parse_from`]), extended
/// syntax such as `(A / B)` and `[A]` is accepted and normalized into additional
/// named nonterminals (e.g. `__anon0`), so that the resulting grammar uses only
/// [`Term::Terminal`] and [`Term::Nonterminal`].
///
/// # Normalization (before and after)
///
/// Input text may use parentheses and brackets; the stored grammar is always in
/// normalized form (plain nonterminals and terminals only). Formatting the grammar
/// back to a string shows the normalized form:
///
/// ```rust
/// use bnf::Grammar;
///
/// // Before: extended syntax in the input string
/// let input = r#"<s> ::= (<a> | <b>) [<c>]
/// <a> ::= 'a'
/// <b> ::= 'b'
/// <c> ::= 'c'"#;
///
/// let grammar: Grammar = input.parse().unwrap();
///
/// // After: normalization replaces ( ) and [ ] with __anon* nonterminals
/// let normalized = format!("{}", grammar);
/// assert!(normalized.contains("__anon"));
/// assert!(!normalized.contains('('));  // no groups in output
/// assert!(!normalized.contains('[')); // no optionals in output
/// # // Example of what normalized might look like (exact names may vary):
/// # // <s> ::= <__anon0> <__anon1>
/// # // <__anon0> ::= <a> | <b>
/// # // <__anon1> ::= <c> | ''
/// # // <a> ::= 'a'
/// # // ...
/// ```
///
/// The library fully supports Unicode throughout all operations, including Unicode
/// characters in terminals, nonterminals, input strings, and generated output.
#[derive(Clone, Default, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct Grammar {
    productions: Vec<Production>,
}

impl Grammar {
    /// Construct a new `Grammar`
    #[must_use]
    pub const fn new() -> Grammar {
        Grammar {
            productions: vec![],
        }
    }

    /// Construct a `Grammar` from `Production`s
    #[must_use]
    pub const fn from_parts(v: Vec<Production>) -> Grammar {
        Grammar { productions: v }
    }

    /// parse a grammar given a format
    pub fn parse_from<F: Format>(input: &str) -> Result<Self, self::Error> {
        match parsers::grammar_complete::<F>(input) {
            Ok((_, g)) => Ok(g),
            Err(e) => Err(Error::from(e)),
        }
    }

    /// Add `Production` to the `Grammar`
    pub fn add_production(&mut self, prod: Production) {
        self.productions.push(prod);
    }

    /// Remove `Production` from the `Grammar`
    pub fn remove_production(&mut self, prod: &Production) -> Option<Production> {
        self.productions
            .iter()
            .position(|x| *x == *prod)
            .map(|pos| self.productions.swap_remove(pos))
    }

    /// Get iterator of the `Grammar`'s `Production`s
    pub fn productions_iter(&self) -> impl Iterator<Item = &Production> {
        self.productions.iter()
    }

    /// Get mutable iterator of the `Grammar`'s `Production`s
    pub fn productions_iter_mut(&mut self) -> impl Iterator<Item = &mut Production> {
        self.productions.iter_mut()
    }

    /// Validate the `Grammar` has no undefined nonterminals
    ///
    /// No need to call this method before building a parser, as the parser will validate the grammar at construction time.
    ///
    /// # Errors
    ///
    /// Returns `Error::ValidationError` if the grammar has no productions or has undefined nonterminals.
    pub fn validate(&self) -> Result<(), Error> {
        if self.productions.is_empty() {
            return Err(Error::ValidationError(
                "Grammar must have at least one production".to_string(),
            ));
        }
        let mut sets = crate::validation::NonterminalSets::new();
        for production in self.productions_iter() {
            if let Term::Nonterminal(nt) = &production.lhs {
                sets.record_lhs(nt.as_str());
            }
            for expression in production.rhs_iter() {
                for term in expression.terms_iter() {
                    if let Term::Nonterminal(nt) = term {
                        sets.record_rhs(nt.as_str());
                    }
                }
            }
        }
        if let Some(undefined) = sets.undefined().next() {
            return Err(Error::ValidationError(format!(
                "Undefined nonterminals: <{undefined}>"
            )));
        }
        Ok(())
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
    /// let parser = grammar.build_parser()?;
    /// let parse_trees: Vec<_> = parser.parse_input("GATTACA").collect();
    /// # Ok::<(), bnf::Error>(())
    /// ```
    pub fn build_parser(&self) -> Result<crate::GrammarParser<'_>, Error> {
        crate::GrammarParser::new(self)
    }

    /// Parse input strings according to `Grammar`
    ///
    /// # Deprecated
    ///
    /// This method is deprecated. Use [`crate::GrammarParser`] instead, which validates
    /// all nonterminals at construction time and allows reusing the parser for
    /// multiple inputs.
    ///
    /// ```rust,no_run
    /// # use bnf::Grammar;
    /// # let grammar: Grammar = "<dna> ::= <base>".parse().unwrap();
    /// let parser = grammar.build_parser()?;
    /// let parse_trees: Vec<_> = parser.parse_input("input").collect();
    /// # Ok::<(), bnf::Error>(())
    /// ```
    #[deprecated(
        since = "0.6.0",
        note = "Use Grammar::build_parser() and GrammarParser::parse_input() instead for validation and reusability"
    )]
    pub fn parse_input<'gram>(
        &'gram self,
        input: &'gram str,
    ) -> impl Iterator<Item = ParseTree<'gram>> {
        let parser = Rc::new(crate::GrammarParser::new_unchecked(self));
        crate::earley::parse_with_parser_rc(parser, input, None)
    }

    /// Parse input strings according to `Grammar`, starting with given production
    ///
    /// # Deprecated
    ///
    /// This method is deprecated. Use [`crate::GrammarParser`] instead, which validates
    /// all nonterminals at construction time and allows reusing the parser for
    /// multiple inputs.
    ///
    /// ```rust,no_run
    /// # use bnf::{Grammar, Term};
    /// # let grammar: Grammar = "<dna> ::= <base>".parse().unwrap();
    /// let parser = grammar.build_parser()?;
    /// let start = Term::Nonterminal("dna".to_string());
    /// let parse_trees: Vec<_> = parser.parse_input_starting_with("input", &start).collect();
    /// # Ok::<(), bnf::Error>(())
    /// ```
    #[deprecated(
        since = "0.6.0",
        note = "Use Grammar::build_parser() and GrammarParser::parse_input_starting_with() instead for validation and reusability"
    )]
    pub fn parse_input_starting_with<'gram>(
        &'gram self,
        input: &'gram str,
        starting_term: &'gram Term,
    ) -> impl Iterator<Item = ParseTree<'gram>> {
        let parser = Rc::new(crate::GrammarParser::new_unchecked(self));
        crate::earley::parse_with_parser_rc(parser, input, Some(starting_term))
    }

    /// Get the starting term
    pub(crate) fn starting_term(&self) -> Option<&Term> {
        self.productions_iter().next().map(|prod| &prod.lhs)
    }

    fn eval_terminal(
        &self,
        term: &Term,
        rng: &mut StdRng,
        f: &impl Fn(&str, &str) -> bool,
    ) -> Result<String, Error> {
        match term {
            Term::Nonterminal(nt) => self.traverse(nt, rng, f),
            Term::Terminal(t) => Ok(t.clone()),
        }
    }

    fn traverse(
        &self,
        ident: &str,
        rng: &mut StdRng,
        f: &impl Fn(&str, &str) -> bool,
    ) -> Result<String, Error> {
        loop {
            let nonterm = Term::Nonterminal(ident.to_string());
            let find_lhs = self.productions_iter().find(|&x| x.lhs == nonterm);

            let Some(production) = find_lhs else {
                return Ok(nonterm.to_string());
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
        if !self.terminates() {
            return Err(Error::GenerateError(
                "Can't generate, first rule in grammar doesn't lead to a terminal state"
                    .to_string(),
            ));
        }

        let start_rule = match self.productions_iter().next() {
            Some(term) => match &term.lhs {
                Term::Nonterminal(nt) => nt.clone(),
                Term::Terminal(_) => {
                    return Err(Error::GenerateError(format!(
                        "Terminal type cannot define a production in '{term}'!"
                    )));
                }
            },
            None => {
                return Err(Error::GenerateError(String::from(
                    "Failed to get first production!",
                )));
            }
        };
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

impl fmt::Display for Grammar {
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

impl str::FromStr for Grammar {
    type Err = Error;
    #[cfg(feature = "ABNF")]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        //try and autodetect the format (in the feature we'll use a detector that returns an enum, hence the gratuitous switch case)
        match parsers::is_format_standard_bnf(s) {
            true => match parsers::grammar_complete::<BNF>(s) {
                Ok((_, g)) => Ok(g),
                Err(e) => Err(Error::from(e)),
            },
            false => match parsers::grammar_complete::<ABNF>(s) {
                Ok((_, g)) => Ok(g),
                Err(e) => Err(Error::from(e)),
            },
        }
    }
    #[cfg(not(feature = "ABNF"))]
    #[mutants::skip]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parsers::grammar_complete::<BNF>(s) {
            Ok((_, g)) => Ok(g),
            Err(e) => Err(Error::from(e)),
        }
    }
}

/// Construct a `Grammar` from a series of semicolon separated productions.
/// ```
/// bnf::grammar! {
///   <dna> ::= <base> | <base> <dna>;
///   <base> ::= 'A' | 'C' | 'G' | 'T';
/// };
/// ```
#[macro_export]
macro_rules! grammar {
    // empty grammar
    () => {
        $crate::Grammar::new()
    };
    // Entry: start collecting productions
    (<$lhs:ident> ::= $($rest:tt)*) => {
        {
            // State: [current_terms_vec, current_exprs_nested_vecs, current_lhs, completed_productions_nested]
            let productions = $crate::grammar!(@collect_prods [[] [] [$lhs]] $($rest)*);
            $crate::Grammar::from_parts(productions)
        }
    };

    // Hit semicolon followed by another production
    (@collect_prods [[$($curr_terms:expr),*] [$($curr_exprs:tt)*] [$curr_lhs:ident] $($prev_prods:tt)*] ; <$next_lhs:ident> ::= $($rest:tt)*) => {
        {
            // Save current production and start next one
            $crate::grammar!(@collect_prods [[] [] [$next_lhs] [[$($curr_terms),*] $($curr_exprs)*] [$curr_lhs] $($prev_prods)*] $($rest)*)
        }
    };

    // Hit semicolon at end (no more productions)
    (@collect_prods [[$($curr_terms:expr),*] [$($curr_exprs:tt)*] [$curr_lhs:ident] $($prev_prods:tt)*] ;) => {
        $crate::grammar!(@collect_prods [[$($curr_terms),*] [$($curr_exprs)*] [$curr_lhs] $($prev_prods)*])
    };

    // Hit | within a production - finish current expression, start new one
    (@collect_prods [[$($curr_terms:expr),*] [$($curr_exprs:tt)*] [$lhs:ident] $($prev_prods:tt)*] | $($rest:tt)*) => {
        $crate::grammar!(@collect_prods [[] [[$($curr_terms),*] $($curr_exprs)*] [$lhs] $($prev_prods)*] $($rest)*)
    };

    // Collect a literal term
    (@collect_prods [[$($curr_terms:expr),*] $($state:tt)*] $t:literal $($rest:tt)*) => {
        $crate::grammar!(@collect_prods [[$($curr_terms,)* $crate::term!($t)] $($state)*] $($rest)*)
    };

    // Collect a nonterminal
    (@collect_prods [[$($curr_terms:expr),*] $($state:tt)*] <$nt:ident> $($rest:tt)*) => {
        $crate::grammar!(@collect_prods [[$($curr_terms,)* $crate::term!(<$nt>)] $($state)*] $($rest)*)
    };

    // Base case - no more tokens, build all productions
    (@collect_prods [[$($last_terms:expr),*] [$($last_exprs:tt)*] [$last_lhs:ident] $([$($prod_exprs:tt)*] [$prod_lhs:ident])*]) => {
        {
            #[allow(clippy::vec_init_then_push)]
            {
                let mut prods = vec![];

                // Build previous productions (in reverse order since we accumulated backwards)
                $(
                    let mut exprs = vec![];
                    $crate::grammar!(@build_exprs exprs $($prod_exprs)*);
                    prods.push($crate::Production::from_parts(
                        $crate::term!(<$prod_lhs>),
                        exprs,
                    ));
                )*

                // Build last production
                let mut last_exprs = vec![];
                $crate::grammar!(@build_exprs last_exprs $($last_exprs)* [$($last_terms),*]);
                prods.push($crate::Production::from_parts(
                    $crate::term!(<$last_lhs>),
                    last_exprs,
                ));

                prods
            }
        }
    };

    // Helper to build expressions vector from nested term arrays
    (@build_exprs $exprs:ident $([$($terms:expr),*])*) => {
        #[allow(clippy::vec_init_then_push)]
        {
            $(
                $exprs.push($crate::Expression::from_parts(vec![$($terms),*]));
            )*
        }
    };
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use super::*;
    use crate::expression::Expression;
    use crate::production::Production;
    use crate::term::Term;
    use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};

    impl Arbitrary for Grammar {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut productions = Vec::<Production>::arbitrary(g);
            // grammar must always have atleast one production
            if productions.is_empty() {
                productions.push(Production::arbitrary(g));
            }
            Grammar { productions }
        }
    }

    fn prop_to_string_and_back(gram: Grammar) -> TestResult {
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
            .quickcheck(prop_to_string_and_back as fn(Grammar) -> TestResult);
    }

    #[test]
    fn new_grammars() {
        let lhs1 = Term::Nonterminal(String::from("STRING A"));
        let rhs1 = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
        ]);
        let p1 = Production::from_parts(lhs1, vec![rhs1]);

        let lhs2 = Term::Nonterminal(String::from("STRING A"));
        let rhs2 = Expression::from_parts(vec![
            Term::Terminal(String::from("STRING B")),
            Term::Nonterminal(String::from("STRING C")),
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
    fn validate_fails_for_empty_grammar() {
        let grammar = Grammar::from_parts(vec![]);
        let result = grammar.validate();
        assert!(result.is_err(), "validate should fail for empty grammar");
        assert!(matches!(result.unwrap_err(), Error::ValidationError(_)));
    }

    #[test]
    fn validate_succeeds_for_valid_grammar() {
        let grammar: Grammar = "<start> ::= <a> | <b>
            <a> ::= 'a'
            <b> ::= 'b'"
            .parse()
            .unwrap();
        assert!(grammar.validate().is_ok());
    }

    #[test]
    fn validate_fails_for_undefined_nonterminal() {
        let grammar: Grammar = "<start> ::= <a> | <b>
            <a> ::= 'a'"
            .parse()
            .unwrap();
        let result = grammar.validate();
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), Error::ValidationError(_)));
    }

    #[test]
    fn validate_error_message_contains_undefined_nonterminal() {
        let grammar: Grammar = "<start> ::= <undefined_nt>".parse().unwrap();
        let err = grammar.validate().unwrap_err();
        let Error::ValidationError(msg) = err else {
            panic!("expected ValidationError");
        };
        assert!(
            msg.contains("<undefined_nt>"),
            "message should mention undefined nonterminal: {msg}"
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
    fn lhs_is_terminal_parse() {
        let grammar: Result<Grammar, _> = "\"wrong place\" ::= <not-used>".parse();
        assert!(grammar.is_err(), "{grammar:?} should be error");
    }

    #[test]
    fn lhs_is_terminal_generate() {
        let lhs = Term::Terminal(String::from("\"bad LHS\""));
        let terminal = Term::Terminal(String::from("\"good RHS\""));
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
        let lhs = Term::Terminal(String::from("<good-lhs>"));
        let production = Production::from_parts(lhs, vec![]);
        let grammar = Grammar::from_parts(vec![production]);
        let sentence = grammar.generate();
        assert!(sentence.is_err(), "{sentence:?} should be error");
    }

    #[test]
    fn generate_with_groups_and_optionals() {
        // Grammar with extended syntax ( ) and [ ] is normalized; generate() should still work
        let grammar: Grammar = "
        <s> ::= (<a> | <b>) [<c>]
        <a> ::= 'a'
        <b> ::= 'b'
        <c> ::= 'c'"
            .parse()
            .unwrap();
        let valid: crate::HashSet<String> = ["a", "b", "ac", "bc"]
            .into_iter()
            .map(String::from)
            .collect();
        for _ in 0..50 {
            let s = grammar.generate().expect("generate should succeed");
            assert!(
                valid.contains(&s),
                "generated '{s}' should be one of a, b, ac, bc"
            );
        }
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
    fn parse_tree_fmt_empty_rhs() {
        // ParseTree allows empty rhs; fmt must not underflow (last_child_idx = len - 1).
        let lhs = Term::Nonterminal("root".to_string());
        let tree = ParseTree::new(&lhs, vec![]);
        let s = tree.to_string();
        assert!(s.contains("root"));
        assert!(s.contains("::="));
    }

    #[test]
    fn parse_tree_fmt_single_child() {
        let lhs = Term::Nonterminal("root".to_string());
        let child = ParseTreeNode::Terminal("x");
        let tree = ParseTree::new(&lhs, vec![child]);
        let s = tree.to_string();
        assert!(s.contains("root"));
        assert!(s.contains("::="));
        assert!(s.contains("\"x\""));
    }

    #[test]
    fn iterate_parse_tree() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parse_tree = grammar.parse_input(input).next().unwrap();

        let rhs_iterated = parse_tree.rhs_iter().next().unwrap();

        assert_eq!(parse_tree.rhs.first().unwrap(), rhs_iterated);
    }

    #[test]
    fn iterate_mut_parse_tree() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= 'A' | 'C' | 'G' | 'T'"
            .parse()
            .unwrap();

        let input = "GATTACA";

        let mut parse_tree = grammar.parse_input(input).next().unwrap();

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

    #[test]
    fn macro_construct() {
        let grammar = crate::grammar! {
            <dna> ::= <base> | <base> <dna> ;
            <base> ::= 'A' | 'C' | 'G' | 'T' ;
        };
        let expected = crate::grammar! {
            <dna> ::= <base> | <base> <dna> ;
            <base> ::= 'A' | 'C' | 'G' | 'T' ;
        };
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
        let grammar: Grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse()
            .unwrap();

        let input = "😀🎉";
        let mut parse_trees = grammar.parse_input(input);

        assert!(
            parse_trees.next().is_some(),
            "Should parse Unicode input '{input}'"
        );
    }

    #[test]
    fn unicode_parse_tree_display() {
        // Test that parse trees with Unicode display correctly
        let grammar: Grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse()
            .unwrap();

        let input = "😀😍";
        let parse_tree = grammar.parse_input(input).next().unwrap();

        let display = parse_tree.to_string();

        // Should contain Unicode characters in the parse tree display
        assert!(display.contains('😀') || display.contains('😍'));
    }

    #[test]
    fn unicode_parse_tree_iteration() {
        // Test that parse trees with Unicode can be iterated
        let grammar: Grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse()
            .unwrap();

        let input = "😀😍🎉";
        let parse_tree = grammar.parse_input(input).next().unwrap();

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
        let grammar: Grammar = "<text> ::= <emoji> | <emoji> <text>
        <emoji> ::= '😀' | '😍' | '🎉' | '🚀'"
            .parse()
            .unwrap();

        let input = "😀😍";
        let parse_tree = grammar.parse_input(input).next().unwrap();

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
        let grammar: Grammar = "<文本> ::= <表情> | <符号> | <表情> <文本>
        <表情> ::= '😀' | '😍'
        <符号> ::= 'α' | 'β'"
            .parse()
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
        let mut parse_trees = grammar.parse_input(input);
        assert!(
            parse_trees.next().is_some(),
            "Should parse Unicode input with Unicode nonterminals: '{input}'"
        );
    }

    #[test]
    fn parse_starting_with() {
        let grammar: Grammar = "<base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>"
            .parse()
            .unwrap();

        let input = "GATTACA";

        assert!(
            grammar
                .parse_input_starting_with(input, &crate::term!(<dna>))
                .next()
                .is_some()
        );
        assert!(
            grammar
                .parse_input_starting_with(input, &crate::term!(<base>))
                .next()
                .is_none()
        );
    }

    #[test]
    fn parse_starting_with_not_found_production() {
        let grammar: Grammar = "<base> ::= 'A' | 'C' | 'G' | 'T'
        <dna> ::= <base> | <base> <dna>"
            .parse()
            .unwrap();

        let input = "GATTACA";
        assert!(
            grammar
                .parse_input_starting_with(input, &crate::term!(<notfound>))
                .next()
                .is_none()
        )
    }

    #[test]
    fn escape_mermaid_label_identity() {
        assert_eq!(escape_mermaid_label("abc"), "abc");
        assert_eq!(escape_mermaid_label("sum"), "sum");
        assert_eq!(escape_mermaid_label("G"), "G");
    }

    #[test]
    fn escape_mermaid_label_double_quote() {
        assert_eq!(escape_mermaid_label("\""), "#34;");
        assert_eq!(escape_mermaid_label("a\"b"), "a#34;b");
    }

    #[test]
    fn escape_mermaid_label_brackets() {
        assert_eq!(escape_mermaid_label("["), "#91;");
        assert_eq!(escape_mermaid_label("]"), "#93;");
        assert_eq!(escape_mermaid_label("[x]"), "#91;x#93;");
    }

    #[test]
    fn escape_mermaid_label_backslash_and_hash_semicolon() {
        assert_eq!(escape_mermaid_label("\\"), "#92;");
        assert_eq!(escape_mermaid_label("#"), "#35;");
        assert_eq!(escape_mermaid_label(";"), "#59;");
        assert_eq!(escape_mermaid_label("#34;"), "#35;34#59;");
    }

    #[test]
    fn escape_mermaid_label_angle_brackets_and_ampersand() {
        assert_eq!(escape_mermaid_label("<"), "#60;");
        assert_eq!(escape_mermaid_label(">"), "#62;");
        assert_eq!(escape_mermaid_label("&"), "#38;");
        assert_eq!(escape_mermaid_label("<foo>"), "#60;foo#62;");
        assert_eq!(escape_mermaid_label("a&b"), "a#38;b");
    }

    #[test]
    fn escape_mermaid_label_newlines() {
        assert_eq!(escape_mermaid_label("\n"), "#10;");
        assert_eq!(escape_mermaid_label("\r"), "#13;");
        assert_eq!(escape_mermaid_label("a\nb"), "a#10;b");
    }

    #[test]
    fn escape_mermaid_label_mixed() {
        assert_eq!(
            escape_mermaid_label(r#"["];\#""#),
            "#91;#34;#93;#59;#92;#35;#34;"
        );
    }

    #[test]
    fn mermaid_entity_codes_double_quote_in_label() {
        let grammar: Grammar = r#"<q> ::= '"'"#.parse().unwrap();
        let input = "\"";
        let parse_tree = grammar.parse_input(input).next().unwrap();
        let mermaid = parse_tree.mermaid().to_string();
        // Label for terminal " must be escaped as #34;, so line has exactly 4 quotes (two node wrappers).
        assert!(
            mermaid.contains("#34;"),
            "mermaid should escape quote as #34;"
        );
        for line in mermaid.lines() {
            if line.contains("-->") {
                let quote_count = line.matches('"').count();
                assert_eq!(
                    quote_count, 4,
                    "each edge line must have 4 quotes (balanced labels); line: {line:?}"
                );
            }
        }
    }

    #[test]
    fn mermaid_entity_codes_brackets_in_label() {
        let grammar: Grammar = "<b> ::= ']' | '['
        "
        .parse()
        .unwrap();
        for input in ["]", "["] {
            let parse_tree = grammar.parse_input(input).next().unwrap();
            let mermaid = parse_tree.mermaid().to_string();
            assert!(
                mermaid.contains("#91;") || mermaid.contains("#93;"),
                "mermaid should escape brackets"
            );
            for line in mermaid.lines() {
                if line.contains("-->") {
                    let quote_count = line.matches('"').count();
                    assert_eq!(quote_count, 4, "line: {line:?}");
                }
            }
        }
    }
}
