#![allow(clippy::vec_init_then_push)]

use crate::error::Error;
use crate::expression::Expression;
use crate::parsers;
use crate::production::Production;
use crate::term::Term;
use rand::{Rng, SeedableRng, rng, rngs::StdRng, seq::IndexedRandom};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use std::fmt;
use std::str;

/// A node of a `ParseTree`, either terminating or continuing the `ParseTree`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseTreeNode<'gram> {
    Terminal(&'gram str),
    Nonterminal(ParseTree<'gram>),
}

/// A tree derived by successfully parsing an input string via [`Grammar::parse_input`]
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
type ParseTreeFormatSet = std::collections::HashSet<usize>;

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
    /// let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
    /// <base> ::= 'A' | 'C' | 'G' | 'T'"
    /// .parse()
    /// .unwrap();
    ///
    /// let input = "GATTACA";
    /// let parsed = grammar.parse_input(input).next().unwrap();
    /// let mermaid = parsed.mermaid().to_string();
    /// println!("parse tree mermaid: {}", mermaid);
    /// ```
    #[must_use]
    pub const fn mermaid(&self) -> MermaidParseTree<'_> {
        MermaidParseTree { parse_tree: self }
    }

    /// Iterate the "right hand side" parse tree nodes
    pub fn rhs_iter(&self) -> impl Iterator<Item = &ParseTreeNode> {
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

/// Wrap `ParseTree` in "Mermaid" type, which opts into new implementation of `std::fmt::Display`.
/// Writes `ParseTree` as [Mermaid.js](https://mermaid-js.github.io/) flowchart.
pub struct MermaidParseTree<'a> {
    parse_tree: &'a ParseTree<'a>,
}

impl MermaidParseTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, count: &mut usize) -> fmt::Result {
        if *count == 0 {
            writeln!(f, "flowchart TD")?;
        }

        // write line for each child
        // A --> B
        // A --> C
        // id1([This is the text in the box])
        let lhs = match self.parse_tree.lhs {
            Term::Nonterminal(str) => str,
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
                        Term::Nonterminal(str) => str,
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

impl fmt::Display for MermaidParseTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut count = 0usize;
        self.fmt(f, &mut count)
    }
}

/// A Grammar is comprised of any number of Productions
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

    /// Construct an `Grammar` from `Production`s
    #[must_use]
    pub const fn from_parts(v: Vec<Production>) -> Grammar {
        Grammar { productions: v }
    }

    /// parse a grammar given a format
    pub fn parse_from(input: &str) -> Result<Self, self::Error> {
        match parsers::grammar_complete(input) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
        }
    }

    /// Add `Production` to the `Grammar`
    pub fn add_production(&mut self, prod: Production) {
        self.productions.push(prod);
    }

    /// Remove `Production` from the `Grammar`
    pub fn remove_production(&mut self, prod: &Production) -> Option<Production> {
        if let Some(pos) = self.productions.iter().position(|x| *x == *prod) {
            Some(self.productions.remove(pos))
        } else {
            None
        }
    }

    /// Get iterator of the `Grammar`'s `Production`s
    pub fn productions_iter(&self) -> impl Iterator<Item = &Production> {
        self.productions.iter()
    }

    /// Get mutable iterator of the `Grammar`'s `Production`s
    pub fn productions_iter_mut(&mut self) -> impl Iterator<Item = &mut Production> {
        self.productions.iter_mut()
    }

    /// Parse input strings according to `Grammar`
    pub fn parse_input<'gram>(
        &'gram self,
        input: &'gram str,
    ) -> impl Iterator<Item = ParseTree<'gram>> {
        crate::earley::parse(self, input)
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
    /// # Example
    ///
    /// ```rust
    /// use rand::{SeedableRng, rngs::StdRng};
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
            Some(term) => match term.lhs {
                Term::Nonterminal(ref nt) => start_rule = nt.clone(),
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
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parsers::grammar_complete(s) {
            Result::Ok((_, o)) => Ok(o),
            Result::Err(e) => Err(Error::from(e)),
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
    // start productions
    (<$lhs:ident> ::= $($rest:tt)*) => {
        {
            let mut prods = vec![];
            let mut exprs = vec![];
            let mut terms = vec![];
            $crate::grammar!(@rhs prods exprs terms $lhs $($rest)*);
            $crate::Grammar::from_parts(prods)
        }
    };
    // start a new production (after the first)
    (@lhs $prods:ident $expr:ident $terms:ident <$lhs:ident> ::= $($rest:tt)*) => {
        $terms = vec![];
        $expr = vec![];
        $crate::grammar!(@rhs $prods $expr $terms $lhs $($rest)*);
    };
    // end of productions is a NOOP
    (@lhs $prods:ident $exprs:ident $terms:ident) => { };
    // munch rhs until semicolon
    (@rhs $prods:ident $expr:ident $terms:ident $lhs:ident ; $($rest:tt)*) => {
        $expr.push($crate::Expression::from_parts($terms));
        $prods.push($crate::Production::from_parts($crate::term!(<$lhs>), $expr));
        $crate::grammar!(@lhs $prods $expr $terms $($rest)*);
    };
    // if terminal add to expression
    (@rhs $prods:ident $expr:ident $terms:ident $lhs:ident $t:literal $($rest:tt)*) => {
        $terms.push($crate::term!($t));
        $crate::grammar!(@rhs $prods $expr $terms $lhs $($rest)*);
    };
    // if nonterminal add to expression
    (@rhs $prods:ident $expr:ident $terms:ident $lhs:ident <$nt:ident> $($rest:tt)*) => {
        $terms.push($crate::term!(<$nt>));
        $crate::grammar!(@rhs $prods $expr $terms $lhs $($rest)*);
    };
    // if | add expression to production, create new expression
    (@rhs $prods:ident $expr:ident $terms:ident $lhs:ident | $($rest:tt)*) => {
        $expr.push($crate::Expression::from_parts($terms));
        $terms = vec![];
        $crate::grammar!(@rhs $prods $expr $terms $lhs $($rest)*);
    };
}

#[cfg(test)]
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
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let production = Production::from_parts(lhs, expression_list);
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
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let production = Production::from_parts(lhs, expression_list);
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
        let lhs = Term::Nonterminal(String::from("dna"));
        let last = Expression::from_parts(vec![Term::Terminal(String::from("base"))]);
        let one_more = Expression::from_parts(vec![
            Term::Terminal(String::from("base")),
            Term::Nonterminal(String::from("dna")),
        ]);
        let expression_list = vec![last, one_more];
        let production = Production::from_parts(lhs, expression_list);
        let productions = vec![production.clone()];
        let mut grammar = Grammar::from_parts(productions.clone());

        let unused = Production::from_parts(Term::Nonterminal(String::from("nonexistent")), vec![]);

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
        let expected = Grammar::from_parts(vec![
            Production::from_parts(
                Term::Nonterminal(String::from("dna")),
                vec![
                    Expression::from_parts(vec![Term::Nonterminal(String::from("base"))]),
                    Expression::from_parts(vec![
                        Term::Nonterminal(String::from("base")),
                        Term::Nonterminal(String::from("dna")),
                    ]),
                ],
            ),
            Production::from_parts(
                Term::Nonterminal(String::from("base")),
                vec![
                    Expression::from_parts(vec![Term::Terminal(String::from("A"))]),
                    Expression::from_parts(vec![Term::Terminal(String::from("C"))]),
                    Expression::from_parts(vec![Term::Terminal(String::from("G"))]),
                    Expression::from_parts(vec![Term::Terminal(String::from("T"))]),
                ],
            ),
        ]);
        assert_eq!(grammar, expected);
    }
}
