

use node::{Expression, Grammar, Production, Term};
use rand::{thread_rng, Rng};

pub fn get_terminal(grammar: Grammar, term: Term) -> String {
    match term {
        Term::Nonterminal(nt) => traverse(grammar, nt),
        Term::Terminal(t) => t,
    }
}

pub fn choose_from_production(production: Production) -> Term {
    let expression = *thread_rng()
        .choose(&production.rhs_iter().collect::<Vec<&Expression>>())
        .unwrap();

    choose_from_expression(expression.clone())
}

pub fn choose_from_expression(expr: Expression) -> Term {
    let term = *thread_rng()
        .choose(expr.terms_iter().collect::<Vec<&Term>>().as_slice())
        .unwrap();

    term.clone()
}

pub fn traverse(grammar: Grammar, ident: String) -> String {
    let production = grammar
        .productions_iter()
        .find(|&x| x.lhs == Term::Nonterminal(ident.clone()))
        .unwrap()
        .clone();

    get_terminal(grammar, choose_from_production(production));

    String::new()
}
