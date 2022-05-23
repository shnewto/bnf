use crate::{Expression, Grammar, Production, Term};

struct EarleyState {}

struct EarleyParser {}

impl EarleyParser {
    pub fn new() -> Self {
        EarleyParser {}
    }
}

fn predict(grammar: &Grammar, curr: &EarleyState, next: &str) -> impl Iterator<Item = EarleyState> {
    std::iter::empty()
}

fn scan(grammar: &Grammar, curr: &EarleyState, next: &str) -> impl Iterator<Item = EarleyState> {
    std::iter::empty()
}

fn complete(grammar: &Grammar, curr: &EarleyState) -> impl Iterator<Item = EarleyState> {
    std::iter::empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_dna_grammar() -> Grammar {
        "<dna> ::= <base> | <base> <dna>
    <base> ::= \"A\" | \"C\" | \"G\" | \"T\""
            .parse()
            .unwrap()
    }

    #[test]
    fn earley_parse_dna() {
        let grammar = parse_dna_grammar();
        let input = "G A T A C A".split_whitespace();

        let mut parses = grammar.parse(input);
        assert!(matches!(parses.next(), Some(_)));
    }

    #[test]
    fn earley_parse_alien_dna() {
        let grammar = parse_dna_grammar();
        let input = "L O L O L O L".split_whitespace();

        let mut parses = grammar.parse(input);
        assert!(matches!(parses.next(), None));
    }

    #[test]
    fn predict_none() {
        let grammar = parse_dna_grammar();
        todo!()
    }

    #[test]
    fn scan() {
        todo!()
    }

    #[test]
    fn complete() {
        todo!()
    }
}
