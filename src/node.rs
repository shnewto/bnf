use std::fmt;


#[derive(PartialEq, Debug, Clone)]
/// A Term can represent a Terminal or Nonterminal node
pub enum Term {
    Terminal(String),
    Nonterminal(String),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Term::Terminal(ref s) => write!(f, "\"{}\"", s),
            Term::Nonterminal(ref s) => write!(f, "<{}>", s),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
/// An Expression is comprised of any number of Terms
pub struct Expression {
    pub terms: Vec<Term>,
}

impl Expression {
    #[allow(dead_code)]
    pub fn new() -> Expression {
        Expression { terms: vec![] }
    }

    #[allow(dead_code)]
    pub fn from_parts(v: Vec<Term>) -> Expression {
        Expression { terms: v }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let display = self.terms
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(" ");

        write!(f, "{}", display)
    }
}

#[derive(PartialEq, Debug, Clone)]
/// A Production is comprised of any number of Expressions
pub struct Production {
    pub lhs: Term,
    pub rhs: Vec<Expression>,
}

impl Production {
    #[allow(dead_code)]
    pub fn new() -> Production {
        Production {
            lhs: Term::Nonterminal(String::new()),
            rhs: vec![],
        }
    }

    #[allow(dead_code)]
    pub fn from_parts(t: Term, e: Vec<Expression>) -> Production {
        Production { lhs: t, rhs: e }
    }
}

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ::= {};",
            self.lhs.to_string(),
            self.rhs
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(" | ")
        )
    }
}

#[derive(PartialEq, Debug, Clone)]
/// A Grammar is comprised of any number of Productions
pub struct Grammar {
    pub productions: Vec<Production>,
}

impl Grammar {
    pub fn new() -> Grammar {
        Grammar {
            productions: vec![],
        }
    }

    #[allow(dead_code)]
    pub fn from_parts(v: Vec<Production>) -> Grammar {
        Grammar { productions: v }
    }
}

impl fmt::Display for Grammar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}\n",
            self.productions
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}
