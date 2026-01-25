#![allow(deprecated)]

mod util;

use bnf::Grammar;
use criterion::{Criterion, criterion_group, criterion_main};
use rand::seq::IndexedRandom;

fn examples(c: &mut Criterion) {
    let _tracing = util::init_tracing();

    c.bench_function("parse postal", |b| {
        let input = std::include_str!("../tests/fixtures/postal_address.terminated.input.bnf");
        b.iter(|| input.parse::<Grammar>().unwrap());
    });

    c.bench_function("generate DNA", |b| {
        let input = "<dna> ::= <base> | <base> <dna>
            <base> ::= 'A' | 'C' | 'G' | 'T'";
        let grammar: Grammar = input.parse().unwrap();
        b.iter(|| grammar.generate().unwrap());
    });

    let polish_calc_grammar: Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
    .parse()
    .unwrap();

    // use pseudo random for consistent metrics
    let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
    let random_walk_count = 100usize;
    let random_walks: Vec<_> = (0..random_walk_count)
        .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
        .collect();

    c.bench_function("parse polish calculator", |b| {
        b.iter(|| {
            let input = random_walks.choose(&mut rng).unwrap();
            let parses: Vec<_> = polish_calc_grammar.parse_input(input).collect();
            assert!(!parses.is_empty());
        })
    });

    let infinite_grammar: Grammar = "
    <a> ::= '' | <b>
    <b> ::= <a>"
        .parse()
        .unwrap();

    let input = "";
    let mut group = c.benchmark_group("parse infinite nullable grammar");
    for parse_count in (0usize..=100).step_by(25) {
        group.throughput(criterion::Throughput::Elements(parse_count as u64));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(parse_count),
            &parse_count,
            |b, &parse_count| {
                b.iter(|| {
                    let parses: Vec<_> = infinite_grammar
                        .parse_input(input)
                        .take(parse_count)
                        .collect();
                    assert_eq!(parses.len(), parse_count);
                })
            },
        );
    }
}

fn new_parser_api(c: &mut Criterion) {
    let _tracing = util::init_tracing();

    // Benchmark parser construction
    c.bench_function("new parser: postal", |b| {
        let grammar: Grammar =
            std::include_str!("../tests/fixtures/postal_address.terminated.input.bnf")
                .parse()
                .unwrap();
        b.iter(|| grammar.build_parser().unwrap());
    });

    c.bench_function("new parser: polish calculator", |b| {
        let grammar: Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
        .parse()
        .unwrap();
        b.iter(|| grammar.build_parser().unwrap());
    });

    // Benchmark parsing with new API
    let postal_grammar: Grammar =
        std::include_str!("../tests/fixtures/postal_address.terminated.input.bnf")
            .parse()
            .unwrap();
    let postal_parser = postal_grammar.build_parser().unwrap();

    // use pseudo random for consistent metrics
    let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
    let random_walk_count = 100usize;
    let random_postal_strings: Vec<_> = (0..random_walk_count)
        .map(|_| postal_grammar.generate_seeded(&mut rng).unwrap())
        .collect();

    c.bench_function("parse postal (new API)", |b| {
        b.iter(|| {
            let input = random_postal_strings.choose(&mut rng).unwrap();
            let parses: Vec<_> = postal_parser.parse_input(input).collect();
            assert!(!parses.is_empty());
        })
    });

    let polish_calc_grammar: Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
    .parse()
    .unwrap();
    let polish_parser = polish_calc_grammar.build_parser().unwrap();

    // use pseudo random for consistent metrics
    let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
    let random_walk_count = 100usize;
    let random_walks: Vec<_> = (0..random_walk_count)
        .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
        .collect();

    c.bench_function("parse polish calculator (new API)", |b| {
        b.iter(|| {
            let input = random_walks.choose(&mut rng).unwrap();
            let parses: Vec<_> = polish_parser.parse_input(input).collect();
            assert!(!parses.is_empty());
        })
    });

    let infinite_grammar: Grammar = "
    <a> ::= '' | <b>
    <b> ::= <a>"
        .parse()
        .unwrap();
    let infinite_parser = infinite_grammar.build_parser().unwrap();
    let input = "";

    let mut group = c.benchmark_group("parse infinite nullable grammar (new API)");
    for parse_count in (0usize..=100).step_by(25) {
        group.throughput(criterion::Throughput::Elements(parse_count as u64));
        group.bench_with_input(
            criterion::BenchmarkId::from_parameter(parse_count),
            &parse_count,
            |b, &parse_count| {
                b.iter(|| {
                    let parses: Vec<_> = infinite_parser
                        .parse_input(input)
                        .take(parse_count)
                        .collect();
                    assert_eq!(parses.len(), parse_count);
                })
            },
        );
    }
    group.finish();

    // Benchmark showing reusability benefit: parse N inputs with a single parser
    let polish_calc_grammar: Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
    .parse()
    .unwrap();

    let mut group = c.benchmark_group("reusable parser: parse N inputs");
    for input_count in [1, 10, 100, 1000] {
        // Old API: construct + parse for each input (simulated by constructing parser each time)
        group.bench_with_input(
            criterion::BenchmarkId::new("old API (construct each time)", input_count),
            &input_count,
            |b, &input_count| {
                let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
                let inputs: Vec<_> = (0..input_count)
                    .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
                    .collect();
                b.iter(|| {
                    for input in &inputs {
                        // Simulate old API: would need to do setup work each time
                        let parses: Vec<_> = polish_calc_grammar.parse_input(input).collect();
                        assert!(!parses.is_empty());
                    }
                })
            },
        );

        // New API: construct once, parse N inputs
        group.bench_with_input(
            criterion::BenchmarkId::new("new API (reuse parser)", input_count),
            &input_count,
            |b, &input_count| {
                let parser = polish_calc_grammar.build_parser().unwrap();
                let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
                let inputs: Vec<_> = (0..input_count)
                    .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
                    .collect();
                b.iter(|| {
                    for input in &inputs {
                        let parses: Vec<_> = parser.parse_input(input).collect();
                        assert!(!parses.is_empty());
                    }
                })
            },
        );
    }
    group.finish();
}

criterion_group!(benches, examples, new_parser_api);
criterion_main!(benches);
