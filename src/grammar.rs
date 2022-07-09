use crate::error::Error;
use crate::expression::Expression;
use crate::parsers;
use crate::production::Production;
use crate::term::Term;
use rand::{rngs::StdRng, seq::SliceRandom, thread_rng, Rng, SeedableRng};
use serde::{Deserialize, Serialize};

use std::fmt;
use std::slice;
use std::str;

/// A node of a `ParseTree`, either terminating or continuing the `ParseTree`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseTreeNode<'gram> {
    Terminal(&'gram str),
    Nonterminal(ParseTree<'gram>),
}

/// A tree derived by successing parsing an input string via [`Grammar::parse_input`]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseTree<'gram> {
    pub lhs: &'gram Term,
    rhs: Vec<ParseTreeNode<'gram>>,
}

impl<'gram> ParseTree<'gram> {
    pub fn new(lhs: &'gram Term, rhs: Vec<ParseTreeNode<'gram>>) -> Self {
        Self { lhs, rhs }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseTreeIter<'gram, 'a> {
    rhs_nodes: &'a [ParseTreeNode<'gram>],
}

impl<'gram, 'a> Iterator for ParseTreeIter<'gram, 'a> {
    type Item = &'a ParseTreeNode<'gram>;

    fn next(&mut self) -> Option<Self::Item> {
        self.rhs_nodes.split_first().map(|(first, rest)| {
            self.rhs_nodes = rest;
            first
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseTreeIterMut<'gram, 'a> {
    rhs_nodes: &'a mut [ParseTreeNode<'gram>],
}

impl<'gram, 'a> Iterator for ParseTreeIterMut<'gram, 'a> {
    type Item = &'a mut ParseTreeNode<'gram>;

    fn next(&mut self) -> Option<Self::Item> {
        let rhs_nodes = std::mem::take(&mut self.rhs_nodes);

        rhs_nodes.split_first_mut().map(|(first, rest)| {
            self.rhs_nodes = rest;
            first
        })
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
                ParseTreeNode::Terminal(terminal) => write!(f, " \"{}\"", terminal)?,
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
                    writeln!(f, "\"{}\"", terminal)?;
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
            write!(f, "{}", prefix)?;
        }

        Ok(())
    }

    /// Opt into formatting as [Mermaid.js](https://mermaid-js.github.io/) flowchart.
    ///
    /// ```
    /// # use bnf::Grammar;
    /// let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
    /// <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
    /// .parse()
    /// .unwrap();
    ///
    /// let input = "GATTACA";
    /// let parsed = grammar.parse_input(input).next().unwrap();
    /// let mermaid = parsed.mermaid().to_string();
    /// println!("parse tree mermaid: {}", mermaid);
    /// ```
    pub fn mermaid(&self) -> MermaidParseTree<'_> {
        MermaidParseTree { parse_tree: self }
    }

    pub fn rhs_iter<'a>(&'a self) -> ParseTreeIter<'gram, 'a> {
        ParseTreeIter {
            rhs_nodes: &self.rhs[..],
        }
    }

    pub fn rhs_iter_mut<'a>(&'a mut self) -> ParseTreeIterMut<'gram, 'a> {
        ParseTreeIterMut {
            rhs_nodes: &mut self.rhs[..],
        }
    }
}

impl<'gram> fmt::Display for ParseTree<'gram> {
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

impl<'a> MermaidParseTree<'a> {
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
            _ => unreachable!(),
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
                        _ => unreachable!(),
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

impl<'a> fmt::Display for MermaidParseTree<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut count = 0usize;
        self.fmt(f, &mut count)
    }
}

/// A Grammar is comprised of any number of Productions
#[derive(Deserialize, Serialize, Clone, Default, Debug, Eq, Hash, PartialEq)]
pub struct Grammar {
    productions: Vec<Production>,
}

impl Grammar {
    /// Construct a new `Grammar`
    pub fn new() -> Grammar {
        Grammar {
            productions: vec![],
        }
    }

    /// Construct an `Grammar` from `Production`s
    pub fn from_parts(v: Vec<Production>) -> Grammar {
        Grammar { productions: v }
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
    pub fn productions_iter(&self) -> Iter {
        Iter {
            iterator: self.productions.iter(),
        }
    }

    /// Get mutable iterator of the `Grammar`'s `Production`s
    pub fn productions_iter_mut(&mut self) -> IterMut {
        IterMut {
            iterator: self.productions.iter_mut(),
        }
    }

    /// Parse input strings according to `Grammar`
    pub fn parse_input<'gram>(&'gram self, input: &'gram str) -> impl Iterator<Item = ParseTree> {
        crate::earley::parse(self, input)
    }

    fn eval_terminal(
        &self,
        term: &Term,
        rng: &mut StdRng,
        f: &impl Fn(&str, &str) -> bool,
    ) -> Result<String, Error> {
        match *term {
            Term::Nonterminal(ref nt) => self.traverse(nt, rng, f),
            Term::Terminal(ref t) => Ok(t.clone()),
        }
    }

    fn traverse(
        &self,
        ident: &str,
        rng: &mut StdRng,
        f: &impl Fn(&str, &str) -> bool,
    ) -> Result<String, Error> {
        loop {
            // If we only have 64KB left, we've hit our tolerable threshold for recursion
            const STACK_RED_ZONE: usize = 64 * 1024;

            if let Some(remaining) = stacker::remaining_stack() {
                if remaining < STACK_RED_ZONE {
                    return Err(Error::RecursionLimit(format!(
                        "Limit for recursion reached processing <{}>!",
                        ident
                    )));
                }
            }

            let nonterm = Term::Nonterminal(ident.to_string());
            let find_lhs = self.productions_iter().find(|&x| x.lhs == nonterm);

            let production = match find_lhs {
                Some(p) => p,
                None => return Ok(nonterm.to_string()),
            };

            let expressions = production.rhs_iter().collect::<Vec<&Expression>>();

            let expression = match expressions.choose(rng) {
                Some(e) => e,
                None => {
                    return Err(Error::GenerateError(String::from(
                        "Couldn't select random Expression!",
                    )));
                }
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
    ///     <base> ::= \"A\" | \"C\" | \"G\" | \"T\"";
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

        match first_production {
            Some(term) => match term.lhs {
                Term::Nonterminal(ref nt) => start_rule = nt.clone(),
                Term::Terminal(_) => {
                    return Err(Error::GenerateError(format!(
                        "Termainal type cannot define a production in '{}'!",
                        term
                    )));
                }
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
    ///     <base> ::= \"A\" | \"C\" | \"G\" | \"T\"";
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
        thread_rng().fill(&mut seed);
        let mut rng: StdRng = SeedableRng::from_seed(seed);
        self.generate_seeded_callback(&mut rng, f)
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

pub struct Iter<'a> {
    iterator: slice::Iter<'a, Production>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Production;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
}

pub struct IterMut<'a> {
    iterator: slice::IterMut<'a, Production>,
}

impl<'a> Iterator for IterMut<'a> {
    type Item = &'a mut Production;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next()
    }
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
            _ => TestResult::error(format!("{} to string and back should be safe", gram)),
        }
    }

    #[test]
    fn to_string_and_back() {
        QuickCheck::new()
            .tests(1000)
            .gen(Gen::new(12usize))
            .quickcheck(prop_to_string_and_back as fn(Grammar) -> TestResult);
    }

    #[test]
    fn new_grammars() {
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
        let p2: Production = Production::from_parts(lhs2, vec![rhs2]);

        let mut g1: Grammar = Grammar::new();
        g1.add_production(p1.clone());
        g1.add_production(p2.clone());
        let g2: Grammar = Grammar::from_parts(vec![p1, p2]);
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
        assert!(grammar.is_err(), "{:?} should be error", grammar);
    }

    #[test]
    fn parse_error_on_incomplete() {
        let result: Result<Grammar, _> = "".parse();
        assert!(result.is_err(), "{:?} should be err", result);
        match result {
            Err(e) => match e {
                Error::ParseError(_) => (),
                e => panic!("should should be Error::ParseError: {:?}", e),
            },
            Ok(s) => panic!("should should be Error::ParseError: {}", s),
        }
    }

    #[test]
    fn recursion_limit() {
        let grammar: Result<Grammar, _> = "<nonterm> ::= <nonterm>".parse();
        assert!(grammar.is_ok(), "{:?} should be ok", grammar);
        let sentence = grammar.unwrap().generate();
        assert!(sentence.is_err(), "{:?} should be err", sentence);
        match sentence {
            Err(e) => match e {
                Error::RecursionLimit(_) => (),
                e => panic!("should should be Error::RecursionLimit: {:?}", e),
            },
            Ok(s) => panic!("should should be Error::RecursionLimit: {}", s),
        }
    }

    #[test]
    fn lhs_not_found() {
        let grammar: Result<Grammar, _> = "<start> ::= <not-used>".parse();
        assert!(grammar.is_ok(), "{:?} should be ok", grammar);
        let sentence = grammar.unwrap().generate();
        assert!(sentence.is_ok(), "{:?} should be ok", sentence);
        assert_eq!(sentence.unwrap(), String::from("<not-used>"));
    }

    #[test]
    fn lhs_is_terminal_parse() {
        let grammar: Result<Grammar, _> = "\"wrong place\" ::= <not-used>".parse();
        assert!(grammar.is_err(), "{:?} should be error", grammar);
    }

    #[test]
    fn lhs_is_terminal_generate() {
        let lhs = Term::Terminal(String::from("\"bad LHS\""));
        let terminal = Term::Terminal(String::from("\"good RHS\""));
        let expression = Expression::from_parts(vec![terminal]);
        let production = Production::from_parts(lhs, vec![expression]);
        let grammar = Grammar::from_parts(vec![production]);
        let sentence = grammar.generate();
        assert!(sentence.is_err(), "{:?} should be error", sentence);
    }

    #[test]
    fn no_productions() {
        let grammar = Grammar::from_parts(vec![]);
        let sentence = grammar.generate();
        assert!(sentence.is_err(), "{:?} should be error", sentence);
    }

    #[test]
    fn no_expressions() {
        let lhs = Term::Terminal(String::from("<good-lhs>"));
        let production = Production::from_parts(lhs, vec![]);
        let grammar = Grammar::from_parts(vec![production]);
        let sentence = grammar.generate();
        assert!(sentence.is_err(), "{:?} should be error", sentence);
    }

    #[test]
    fn parse_dna() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let mut parses = grammar.parse_input(input);
        assert!(matches!(parses.next(), Some(_)));
    }

    #[test]
    fn format_parse_tree() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";
        let parsed = grammar.parse_input(input).next().unwrap();
        let formatted = format!("{}", parsed);
        let expected = "
<dna> ::= <base> <dna>
├── <base> ::= \"G\"
│   └── \"G\"
└── <dna> ::= <base> <dna>
    ├── <base> ::= \"A\"
    │   └── \"A\"
    └── <dna> ::= <base> <dna>
        ├── <base> ::= \"T\"
        │   └── \"T\"
        └── <dna> ::= <base> <dna>
            ├── <base> ::= \"T\"
            │   └── \"T\"
            └── <dna> ::= <base> <dna>
                ├── <base> ::= \"A\"
                │   └── \"A\"
                └── <dna> ::= <base> <dna>
                    ├── <base> ::= \"C\"
                    │   └── \"C\"
                    └── <dna> ::= <base>
                        └── <base> ::= \"A\"
                            └── \"A\"\n"
            .trim_start();

        assert_eq!(formatted, expected);
    }

    #[test]
    fn format_grammar() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();
        let format = format!("{}", grammar);
        assert_eq!(
            format,
            "<dna> ::= <base> | <base> <dna>\n<base> ::= \"A\" | \"C\" | \"G\" | \"T\"\n"
        );
    }

    #[test]
    fn iterate_parse_tree() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let parse_tree = grammar.parse_input(input).next().unwrap();

        let rhs_iterated = parse_tree.rhs_iter().next().unwrap();

        assert_eq!(&parse_tree.rhs[0], rhs_iterated);
    }

    #[test]
    fn iterate_mut_parse_tree() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";

        let mut parse_tree = grammar.parse_input(input).next().unwrap();

        let rhs_iterated = parse_tree.rhs_iter_mut().next().unwrap();

        *rhs_iterated = ParseTreeNode::Terminal("Z");

        assert_eq!(parse_tree.rhs[0], ParseTreeNode::Terminal("Z"));
    }

    #[test]
    fn mermaid_dna_parse_tree() {
        let grammar: Grammar = "<dna> ::= <base> | <base> <dna>
        <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap();

        let input = "GATTACA";
        let parsed = grammar.parse_input(input).next().unwrap();
        let mermaid = parsed.mermaid().to_string();
        let expected = "
flowchart TD
0[\"dna\"] --> 1[\"base\"]
1[\"base\"] --> 2[\"G\"]
0[\"dna\"] --> 3[\"dna\"]
3[\"dna\"] --> 4[\"base\"]
4[\"base\"] --> 5[\"A\"]
3[\"dna\"] --> 6[\"dna\"]
6[\"dna\"] --> 7[\"base\"]
7[\"base\"] --> 8[\"T\"]
6[\"dna\"] --> 9[\"dna\"]
9[\"dna\"] --> 10[\"base\"]
10[\"base\"] --> 11[\"T\"]
9[\"dna\"] --> 12[\"dna\"]
12[\"dna\"] --> 13[\"base\"]
13[\"base\"] --> 14[\"A\"]
12[\"dna\"] --> 15[\"dna\"]
15[\"dna\"] --> 16[\"base\"]
16[\"base\"] --> 17[\"C\"]
15[\"dna\"] --> 18[\"dna\"]
18[\"dna\"] --> 19[\"base\"]
19[\"base\"] --> 20[\"A\"]\n"
            .trim_start();

        assert_eq!(mermaid, expected);
    }

    #[test]
    fn mermaid_math_parse_tree() {
        let grammar: Grammar = "<sum> ::= <sum> <add> <product>
            <sum> ::= <product>
            <product> ::= <product> <mult> <factor>
            <product> ::= <factor>
            <add> ::= \"+\" | \"-\"
            <mult> ::= \"*\" | \"/\"
            <factor> ::= \"(\" <sum> \")\"
            <factor> ::= <number>
            <number> ::= <digit> <number>
            <number> ::= <digit>
            <digit> ::= \"0\" | \"1\" | \"2\" | \"3\" | \"4\" | \"5\" | \"6\" | \"7\" | \"8\" | \"9\"
        ".parse().unwrap();

        let input = "1+(2*3-4)";

        let parsed = grammar.parse_input(input).next().unwrap();
        let mermaid = parsed.mermaid().to_string();
        let expected = "
flowchart TD
0[\"sum\"] --> 1[\"sum\"]
1[\"sum\"] --> 2[\"product\"]
2[\"product\"] --> 3[\"factor\"]
3[\"factor\"] --> 4[\"number\"]
4[\"number\"] --> 5[\"digit\"]
5[\"digit\"] --> 6[\"1\"]
0[\"sum\"] --> 7[\"add\"]
7[\"add\"] --> 8[\"+\"]
0[\"sum\"] --> 9[\"product\"]
9[\"product\"] --> 10[\"factor\"]
10[\"factor\"] --> 11[\"(\"]
10[\"factor\"] --> 12[\"sum\"]
12[\"sum\"] --> 13[\"sum\"]
13[\"sum\"] --> 14[\"product\"]
14[\"product\"] --> 15[\"product\"]
15[\"product\"] --> 16[\"factor\"]
16[\"factor\"] --> 17[\"number\"]
17[\"number\"] --> 18[\"digit\"]
18[\"digit\"] --> 19[\"2\"]
14[\"product\"] --> 20[\"mult\"]
20[\"mult\"] --> 21[\"*\"]
14[\"product\"] --> 22[\"factor\"]
22[\"factor\"] --> 23[\"number\"]
23[\"number\"] --> 24[\"digit\"]
24[\"digit\"] --> 25[\"3\"]
12[\"sum\"] --> 26[\"add\"]
26[\"add\"] --> 27[\"-\"]
12[\"sum\"] --> 28[\"product\"]
28[\"product\"] --> 29[\"factor\"]
29[\"factor\"] --> 30[\"number\"]
30[\"number\"] --> 31[\"digit\"]
31[\"digit\"] --> 32[\"4\"]
10[\"factor\"] --> 33[\")\"]\n"
            .trim_start();

        assert_eq!(mermaid, expected);
    }
}
