use crate::parsers::Format;

#[non_exhaustive]
pub struct ABNF;

impl Format for ABNF {
    fn nonterminal_delimiter() -> Option<(char, char)> {
        None
    }
    fn production_separator() -> &'static str {
        "="
    }
    fn alternative_separator() -> char {
        '/'
    }
}

#[cfg(test)]
mod tests {
    use super::ABNF;
    use crate::parsers::*;

    use crate::expression::Expression;
    use crate::grammar::Grammar;
    use crate::production::Production;
    use crate::term::Term;

    #[test]
    fn nonterminal_match() {
        let input = "nonterminal-pattern";
        let expected = Term::Nonterminal("nonterminal-pattern".to_string());

        let (_, actual) = nonterminal::<ABNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn expression_match() {
        let input = r#"nonterminal-pattern "terminal-pattern""#;
        let expected = Expression::from_parts(vec![
            Term::Nonterminal("nonterminal-pattern".to_string()),
            Term::Terminal("terminal-pattern".to_string()),
        ]);

        let (_, actual) = expression::<ABNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn production_match() {
        let input = r#"nonterminal-pattern = nonterminal-pattern "terminal-pattern" / "terminal-pattern";\r\n"#;
        let expected = Production::from_parts(
            Term::Nonterminal("nonterminal-pattern".to_string()),
            vec![
                Expression::from_parts(vec![
                    Term::Nonterminal("nonterminal-pattern".to_string()),
                    Term::Terminal("terminal-pattern".to_string()),
                ]),
                Expression::from_parts(vec![Term::Terminal("terminal-pattern".to_string())]),
            ],
        );

        let (_, actual) = production::<ABNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn grammar_match() {
        let input = r#"nonterminal-pattern = nonterminal-pattern "terminal-pattern" / "terminal-pattern";\r\n"#;
        let expected = Grammar::from_parts(vec![Production::from_parts(
            Term::Nonterminal("nonterminal-pattern".to_string()),
            vec![
                Expression::from_parts(vec![
                    Term::Nonterminal("nonterminal-pattern".to_string()),
                    Term::Terminal("terminal-pattern".to_string()),
                ]),
                Expression::from_parts(vec![Term::Terminal("terminal-pattern".to_string())]),
            ],
        )]);

        let (_, actual) = grammar::<ABNF>(input).unwrap();
        assert_eq!(expected, actual);
    }
}
