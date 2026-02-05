#![cfg(test)]

mod std_trait {
    use std::str::FromStr;

    use bnf::{Expression, Grammar, Production, Term};

    #[test]
    fn production_is_empty() {
        assert!(Production::new().is_empty());
        let mut p = Production::new();
        p.add_to_rhs(Expression::new());
        assert!(!p.is_empty());
    }

    fn std_str_trait<T: FromStr>(_: T, input: &str) {
        let from_str_result = T::from_str(input);
        assert!(from_str_result.is_ok())
    }

    #[test]
    fn expression_from_str() {
        let input = "'😵' '😋' '😉'";
        let expression = Expression::new();
        std_str_trait(expression, input)
    }

    #[test]
    fn grammar_from_str() {
        let input = "<🙃> ::= '😵' '😋' | '😉'
        <🤘> ::= '👏 ' '👊' | '👌'";
        let grammar = Grammar::new();
        std_str_trait(grammar, input)
    }

    #[test]
    fn production_from_str() {
        let input = "<🤘> ::= '👏 ' '👊' | '👌'";
        let production = Production::new();
        std_str_trait(production, input)
    }

    #[test]
    fn terminal_from_str() {
        let input = "'👏 '";
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

mod custom_trait {
    use bnf::{Expression, Grammar, Production, Term};

    #[test]
    fn expression_from_str() {
        let input = "'😵' '😋' '😉'";
        let expression: Result<Expression, _> = input.parse();
        assert!(expression.is_ok())
    }

    #[test]
    fn grammar_from_str() {
        let input = "<🙃> ::= '😵' '😋' | '😉'
        <🤘> ::= '👏 ' '👊' | '👌'";
        let grammar: Result<Grammar, _> = input.parse();
        assert!(grammar.is_ok())
    }

    #[test]
    fn grammar_from_str_returns_parsed_content() {
        let input = "<a> ::= 'x'";
        let grammar: Grammar = input.parse().expect("parse");
        assert_eq!(
            grammar.productions_iter().count(),
            1,
            "parsed grammar must have one production"
        );
        let prod = grammar.productions_iter().next().unwrap();
        assert_eq!(prod.lhs, bnf::Term::Nonterminal("a".into()));
    }

    #[test]
    fn production_from_str() {
        let input = "<🤘> ::= '👏 ' '👊' | '👌'";
        let production: Result<Production, _> = input.parse();
        assert!(production.is_ok())
    }

    #[test]
    fn terminal_from_str() {
        let input = "'👏 '";
        let terminal: Result<Term, _> = input.parse();
        assert!(terminal.is_ok())
    }

    #[test]
    fn nonterminal_from_str() {
        let input = "<🤘>";
        let nonterminal: Result<Term, _> = input.parse();
        assert!(nonterminal.is_ok())
    }
}

mod comments {
    use bnf::{Grammar, Term};

    #[test]
    fn grammar_with_comments_throughout() {
        let input = "<a> ::= 'x' ; end of first rule
; comment-only line
<b> ::= 'y' ; end of second rule";
        let grammar: Grammar = input.parse().expect("parse");
        assert_eq!(
            grammar.productions_iter().count(),
            2,
            "parsed grammar must have two productions"
        );
        let mut prods = grammar.productions_iter();
        let first = prods.next().unwrap();
        assert_eq!(first.lhs, Term::Nonterminal("a".into()));
        assert_eq!(first.rhs_iter().next().unwrap().to_string(), "'x'");
        let second = prods.next().unwrap();
        assert_eq!(second.lhs, Term::Nonterminal("b".into()));
        assert_eq!(second.rhs_iter().next().unwrap().to_string(), "'y'");
    }

    #[test]
    fn comment_does_not_break_parsing() {
        let input = "<a> ::= 'x' ; note\n<b> ::= 'y'";
        let grammar: Grammar = input.parse().expect("parse");
        assert_eq!(
            grammar.productions_iter().count(),
            2,
            "parsed grammar must have two productions"
        );
        let mut prods = grammar.productions_iter();
        let first = prods.next().unwrap();
        assert_eq!(first.lhs, Term::Nonterminal("a".into()));
        assert_eq!(first.rhs_iter().next().unwrap().to_string(), "'x'");
        let second = prods.next().unwrap();
        assert_eq!(second.lhs, Term::Nonterminal("b".into()));
        assert_eq!(second.rhs_iter().next().unwrap().to_string(), "'y'");
    }
}
