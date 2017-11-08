extern crate bnf;

#[cfg(test)]
mod std_trait {
    use std::str::FromStr;
    
    use bnf::{Expression, Grammar, Production, Term};

    fn std_str_trait<T: FromStr>(_: T, input: &str) {
        let from_str_result = T::from_str(input);
        assert!(from_str_result.is_ok())
    }

    #[test]
    fn expression_from_str() {
        let input = "\"😵\" \"😋\" \"😉\"";
        let expression = Expression::new();
        std_str_trait(expression, input)        
    }

    #[test]
    fn grammar_from_str() {
        let input = "<🙃> ::= \"😵\" \"😋\" | \"😉\"
        <🤘> ::= \"👏 \" \"👊\" | \"👌\"";
        let grammar = Grammar::new();
        std_str_trait(grammar, input)
    }

    #[test]
    fn production_from_str() {
        let input = "<🤘> ::= \"👏 \" \"👊\" | \"👌\"";
        let production = Production::new();
        std_str_trait(production, input)
    }

    #[test]
    fn terminal_from_str() {
        let input = "\"👏 \"";        
        let terminal = Term::Terminal(String::new());
        std_str_trait(terminal, input)
    }

    #[test]
    fn nonterminal_from_str() {
        let input = "<🤘>";        
        let nonterminal = Term::Nonterminal(String::new());
        std_str_trait(nonterminal, input)
    }
}

#[cfg(test)]
mod custom_trait {
    use bnf::{Expression, Grammar, Production, Term};

    #[test]
    fn expression_from_str() {
        let input = "\"😵\" \"😋\" \"😉\"";
        let expression = Expression::from_str(input);
        assert!(expression.is_ok())      
    }

    #[test]
    fn grammar_from_str() {
        let input = "<🙃> ::= \"😵\" \"😋\" | \"😉\"
        <🤘> ::= \"👏 \" \"👊\" | \"👌\"";
        let grammar = Grammar::from_str(input);
        assert!(grammar.is_ok())
    }

    #[test]
    fn production_from_str() {
        let input = "<🤘> ::= \"👏 \" \"👊\" | \"👌\"";
        let production = Production::from_str(input);
        assert!(production.is_ok())
    }

    #[test]
    fn terminal_from_str() {
        let input = "\"👏 \"";        
        let terminal = Term::from_str(input);
        assert!(terminal.is_ok())
    }

    #[test]
    fn nonterminal_from_str() {
        let input = "<🤘>";        
        let nonterminal = Term::from_str(input);
        assert!(nonterminal.is_ok())
    }
}
