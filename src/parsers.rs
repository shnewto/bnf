
use node::{Grammar, Production, Expression, Term,};

named!(pub terminal< &[u8], Term >,
    do_parse!(
        t: delimited!(tag!("\""), take_until!("\""), ws!(tag!("\""))) >>
        (Term::Terminal(String::from_utf8_lossy(t).into_owned()))
    )
);

named!(pub nonterminal< &[u8], Term >,
    do_parse!(
        nt: ws!(delimited!(tag!("<"), take_until_either!(" >"), tag!(">"))) >>
        (Term::Nonterminal(String::from_utf8_lossy(nt).into_owned()))
    )
);

named!(pub expression< &[u8], Expression >,
    do_parse!(
        terms: many1!(alt!(terminal | nonterminal)) >>
        ws!(alt!(tag!(";") | tag!("|"))) >>
        (Expression::from_parts(terms))
    )
);

named!(pub production< &[u8], Production >,
    do_parse!(
        lhs: nonterminal >>
        ws!(tag!("::=")) >>
        rhs: many1!(expression) >>
        (Production::from_parts(lhs, rhs))
    )
);

named!(pub grammar< &[u8], Grammar >,
    do_parse!(
        prods: many1!(production) >>
        eof!() >>
        (Grammar::from_parts(prods))
    )
);    

#[cfg(test)]
mod tests {
    use super::*;

    fn construct_terminal_tuple() -> (Term, String) {
        let terminal_pattern = "\"terminal pattern\"";
        let terminal_value = "terminal pattern";
        let terminal_object =
            Term::Terminal(String::from(terminal_value));

        (terminal_object, String::from(terminal_pattern))
    }

    #[test]
    fn terminal_match() {
        let terminal_tuple = construct_terminal_tuple();
        assert_eq!(terminal_tuple.0,
            terminal(terminal_tuple.1.as_bytes()).unwrap().1);
    }

    fn construct_nonterminal_tuple() -> (Term, String) {
        let nonterminal_pattern = "<nonterminal-pattern>";
        let nonterminal_value = "nonterminal-pattern";
        let nonterminal_object =
            Term::Nonterminal(String::from(nonterminal_value));

        (nonterminal_object, String::from(nonterminal_pattern))
    }

    #[test]
    fn nonterminal_match() {
        let nonterminal_tuple = construct_nonterminal_tuple();
        assert_eq!(nonterminal_tuple.0,
            nonterminal(nonterminal_tuple.1.as_bytes()).unwrap().1);
    }

    fn construct_expression_tuple() -> (Expression, String) {
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = construct_terminal_tuple();
        let expression_pattern = nonterminal_tuple.1 + &terminal_tuple.1 + "|";
        let expression_object =
            Expression::from_parts(vec![nonterminal_tuple.0, terminal_tuple.0]);

        (expression_object, String::from(expression_pattern))
    }

    #[test]
    fn expression_match() {
        let expression_tuple = construct_expression_tuple();
        assert_eq!(expression_tuple.0,
            expression(expression_tuple.1.as_bytes()).unwrap().1);
    }

    fn construct_production_tuple() -> (Production, String) {
        let expression_tuple = construct_expression_tuple();
        let nonterminal_tuple = construct_nonterminal_tuple();
        let terminal_tuple = construct_nonterminal_tuple();
        let production_pattern = 
            nonterminal_tuple.1 + 
            "::=" + 
            &expression_tuple.1 + 
            &terminal_tuple.1 + ";";
        let production_object =
            Production::from_parts(
                nonterminal_tuple.0, 
                vec![expression_tuple.0.clone(), 
                Expression::from_parts(vec![terminal_tuple.0])]);

        (production_object, String::from(production_pattern))
    }

    #[test]
    fn production_match() {
        let production_tuple = construct_production_tuple();
        assert_eq!(production_tuple.0,
            production(production_tuple.1.as_bytes()).unwrap().1);
    }

    fn construct_grammar_tuple() -> (Grammar, String) {

        let production_tuple = construct_production_tuple();
        let grammar_pattern = production_tuple.1.clone() + &production_tuple.1;
        let grammar_object =
            Grammar::from_parts(
                vec![construct_production_tuple().0.clone(), 
                construct_production_tuple().0]);

        (grammar_object, String::from(grammar_pattern))
    }

    #[test]
    fn grammar_match() {
        let grammar_tuple = construct_grammar_tuple();
        println!("{:#?}", grammar_tuple.1);
        assert_eq!(grammar_tuple.0,
            grammar(grammar_tuple.1.as_bytes()).unwrap().1);
    }
}
