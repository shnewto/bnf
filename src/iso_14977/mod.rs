#[derive(Parser)]
#[grammar = "ebnf.pest"]
pub struct CSVParser;

#[cfg(test)]
mod tests {
    use super::*;

    use pest::Parser;

    #[test]
    fn test_config() {
        let successful_parse = CSVParser::parse(Rule::field, "-273.15");
        println!("{:?}", successful_parse);
        let unsuccessful_parse = CSVParser::parse(Rule::field, "this is not a number");
        println!("{:?}", unsuccessful_parse);
    }
}
