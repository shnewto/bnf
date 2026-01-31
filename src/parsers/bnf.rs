use super::Format;

#[non_exhaustive]
pub struct BNF;

impl Format for BNF {
    fn nonterminal_delimiter() -> Option<(char, char)> {
        Some(('<', '>'))
    }
    fn production_separator() -> &'static str {
        "::="
    }
    fn alternative_separator() -> char {
        '|'
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use super::BNF;
    use crate::parsers::*;

    #[test]
    fn nonterminal_match() {
        let input = "<nonterminal-pattern>";
        let expected = Term::Nonterminal(Cow::Owned("nonterminal-pattern".to_string()));

        let (_, actual) = nonterminal::<BNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn expression_match() {
        let input = r#"<nonterminal-pattern> "terminal-pattern""#;
        let expected = Expression::from_parts(vec![
            Term::Nonterminal(Cow::Owned("nonterminal-pattern".to_string())),
            Term::Terminal(Cow::Owned("terminal-pattern".to_string())),
        ]);

        let (_, actual) = expression::<BNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn production_match() {
        let input = r#"<nonterminal-pattern> ::= <nonterminal-pattern> "terminal-pattern" | "terminal-pattern";\r\n"#;
        let expected = Production::from_parts(
            Term::Nonterminal(Cow::Owned("nonterminal-pattern".to_string())),
            vec![
                Expression::from_parts(vec![
                    Term::Nonterminal(Cow::Owned("nonterminal-pattern".to_string())),
                    Term::Terminal(Cow::Owned("terminal-pattern".to_string())),
                ]),
                Expression::from_parts(vec![Term::Terminal(Cow::Owned(
                    "terminal-pattern".to_string(),
                ))]),
            ],
        );

        let (_, actual) = production::<BNF>(input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn grammar_match() {
        let input = r#"<nonterminal-pattern> ::= <nonterminal-pattern> "terminal-pattern" | "terminal-pattern";\r\n"#;
        let expected = Grammar::from_parts(vec![Production::from_parts(
            Term::Nonterminal(Cow::Owned("nonterminal-pattern".to_string())),
            vec![
                Expression::from_parts(vec![
                    Term::Nonterminal(Cow::Owned("nonterminal-pattern".to_string())),
                    Term::Terminal(Cow::Owned("terminal-pattern".to_string())),
                ]),
                Expression::from_parts(vec![Term::Terminal(Cow::Owned(
                    "terminal-pattern".to_string(),
                ))]),
            ],
        )]);

        let (_, actual) = grammar::<BNF>(input).unwrap();
        assert_eq!(expected, actual);
    }
}
