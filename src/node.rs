

#[derive(PartialEq, Debug, Clone)]
/// A Term can represent a Terminal or Nonterminal node
pub enum Term {
    Terminal(String),
    Nonterminal(String),
}

impl ToString for Term {
    fn to_string(&self) -> String {
        match self {
            &Term::Terminal(ref s) => return format!("\"{}\"", s),
            &Term::Nonterminal(ref s) => return format!("<{}>", s),
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
        Expression { terms: vec![], }
    }

    #[allow(dead_code)]
    pub fn from_parts(v: Vec<Term>) -> Expression {
        Expression { terms: v, }
    }
}

impl ToString for Expression {
    fn to_string(&self) -> String {
        self.terms
            .iter()
            .map(|s| s.to_string()).collect::<Vec<_>>().join(" ")
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
        Production { lhs: Term::Nonterminal(String::new()), rhs: vec![], }
    }

    #[allow(dead_code)]
    pub fn from_parts(t: Term, e: Vec<Expression>) -> Production {
        Production { lhs: t, rhs: e, }
    }
}

impl ToString for Production {
    fn to_string(&self) -> String {
        format!(
            "{} ::= {};",
            self.lhs.to_string(),
            self.rhs
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(" | "))
    }
}

#[derive(PartialEq, Debug, Clone)]
/// A Grammar is comprised of any number of Productions
pub struct Grammar {
    pub productions: Vec<Production>,
}

impl Grammar {
    pub fn new() -> Grammar {
        Grammar { productions: vec![], }
    }

    #[allow(dead_code)]
    pub fn from_parts(v: Vec<Production>) -> Grammar {
        Grammar { productions: v, }
    }
}

impl ToString for Grammar {
    fn to_string(&self) -> String {
        format!(
            "{}\n",
            self.productions
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n"))
    }
}
