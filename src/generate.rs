

use node::{Expression, Grammar, Production, Term};
use rand::{thread_rng, Rng};

pub fn get_terminal(grammar: Grammar, term: Term) -> String {
    match term {
        Term::Nonterminal(nt) => traverse(grammar, nt),
        Term::Terminal(t) => {
            println!(" {} ", t);
            return t;
        }
    }
}

pub fn choose_from_production(production: Production) -> Term {
    choose_from_expression(
        thread_rng()
            .choose(*production.rhs_iter().collect())
            .unwrap(),
    )
}

pub fn choose_from_expression(expr: Expression) -> Term {
    thread_rng().choose(expr.terms_iter().collect()).unwrap()
}

pub fn traverse(grammar: Grammar, ident: String) -> String {
    let production = grammar
        .productions_iter()
        .find(|&x| x.lhs == Term::Nonterminal(ident))
        .unwrap();

    get_terminal(grammar, choose_from_production(production));

    String::new()
}
