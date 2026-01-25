#![allow(deprecated)]

mod util;

#[global_allocator]
static ALLOC: divan::AllocProfiler = divan::AllocProfiler::system();

fn main() {
    let _tracing = util::init_tracing();

    #[cfg(feature = "tracing")]
    let _span = tracing::span!(tracing::Level::DEBUG, "BENCH EXAMPLES").entered();

    divan::main();
}

mod examples {
    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_postal(bencher: divan::Bencher) {
        let input = divan::black_box(include_str!(
            "../tests/fixtures/postal_address.terminated.input.bnf"
        ));

        bencher.bench(|| {
            input.parse::<bnf::Grammar>().unwrap();
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_postal_input(bencher: divan::Bencher) {
        let postal_grammar: bnf::Grammar =
            include_str!("../tests/fixtures/postal_address.terminated.input.bnf")
                .parse()
                .unwrap();

        // use pseudo random for consistent metrics
        use rand::seq::SliceRandom;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
        let random_walk_count = 100usize;
        let mut random_postal_strings: Vec<_> = (0..random_walk_count)
            .map(|_| postal_grammar.generate_seeded(&mut rng).unwrap())
            .collect();

        random_postal_strings.shuffle(&mut rng);
        let random_postal_strings = divan::black_box(random_postal_strings);
        let mut index = (0..random_walk_count).cycle();

        bencher.bench_local(|| {
            let index = index.next().unwrap();
            let input = random_postal_strings.get(index).unwrap();
            postal_grammar
                .parse_input(input)
                .for_each(divan::black_box_drop);
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn generate_dna(bencher: divan::Bencher) {
        bencher
            .with_inputs(|| {
                let input = "<dna> ::= <base> | <base> <dna>
            <base> ::= 'A' | 'C' | 'G' | 'T'";
                let grammar: bnf::Grammar = input.parse().unwrap();
                grammar
            })
            .bench_refs(|grammar| {
                grammar.generate().unwrap();
            });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_polish_calculator(bencher: divan::Bencher) {
        let polish_calc_grammar: bnf::Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
        .parse()
        .unwrap();

        // use pseudo random for consistent metrics
        use rand::seq::SliceRandom;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
        let random_walk_count = 100usize;
        let mut random_walks: Vec<_> = (0..random_walk_count)
            .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
            .collect();

        random_walks.shuffle(&mut rng);
        let random_walks = divan::black_box(random_walks);
        let mut index = (0..random_walk_count).cycle();

        bencher.bench_local(|| {
            let index = index.next().unwrap();
            let input = random_walks.get(index).unwrap();
            polish_calc_grammar
                .parse_input(input)
                .for_each(divan::black_box_drop);
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_infinite_nullable_grammar(bencher: divan::Bencher) {
        use rand::Rng;

        let infinite_grammar: bnf::Grammar = "
                <a> ::= '' | <b>
                <b> ::= <a>"
            .parse()
            .unwrap();

        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);

        bencher
            .with_inputs(|| rng.random_range(1..100))
            .count_inputs_as::<divan::counter::ItemsCount>()
            .bench_local_values(|parse_count| {
                infinite_grammar
                    .parse_input("")
                    .take(parse_count)
                    .for_each(divan::black_box_drop);
            });
    }
}

mod new_parser_api {
    #[divan::bench(min_time = 5, max_time = 60)]
    fn new_parser_postal(bencher: divan::Bencher) {
        let grammar = divan::black_box(
            include_str!("../tests/fixtures/postal_address.terminated.input.bnf")
                .parse::<bnf::Grammar>()
                .unwrap(),
        );

        bencher.bench(|| {
            grammar.build_parser().unwrap();
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn new_parser_polish_calculator(bencher: divan::Bencher) {
        let grammar = divan::black_box(
            "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
            .parse::<bnf::Grammar>()
            .unwrap(),
        );

        bencher.bench(|| {
            grammar.build_parser().unwrap();
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_postal_new_api(bencher: divan::Bencher) {
        let postal_grammar: bnf::Grammar =
            include_str!("../tests/fixtures/postal_address.terminated.input.bnf")
                .parse()
                .unwrap();
        let parser = postal_grammar.build_parser().unwrap();

        // use pseudo random for consistent metrics
        use rand::seq::SliceRandom;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
        let random_walk_count = 100usize;
        let mut random_postal_strings: Vec<_> = (0..random_walk_count)
            .map(|_| postal_grammar.generate_seeded(&mut rng).unwrap())
            .collect();

        random_postal_strings.shuffle(&mut rng);
        let random_postal_strings = divan::black_box(random_postal_strings);
        let mut index = (0..random_walk_count).cycle();

        bencher.bench_local(|| {
            let index = index.next().unwrap();
            let input = random_postal_strings.get(index).unwrap();
            parser.parse_input(input).for_each(divan::black_box_drop);
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_polish_calculator_new_api(bencher: divan::Bencher) {
        let polish_calc_grammar: bnf::Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
        .parse()
        .unwrap();
        let parser = polish_calc_grammar.build_parser().unwrap();

        // use pseudo random for consistent metrics
        use rand::seq::SliceRandom;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
        let random_walk_count = 100usize;
        let mut random_walks: Vec<_> = (0..random_walk_count)
            .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
            .collect();

        random_walks.shuffle(&mut rng);
        let random_walks = divan::black_box(random_walks);
        let mut index = (0..random_walk_count).cycle();

        bencher.bench_local(|| {
            let index = index.next().unwrap();
            let input = random_walks.get(index).unwrap();
            parser.parse_input(input).for_each(divan::black_box_drop);
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_infinite_nullable_grammar_new_api(bencher: divan::Bencher) {
        use rand::Rng;

        let infinite_grammar: bnf::Grammar = "
                <a> ::= '' | <b>
                <b> ::= <a>"
            .parse()
            .unwrap();
        let parser = infinite_grammar.build_parser().unwrap();

        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);

        bencher
            .with_inputs(|| rng.random_range(1..100))
            .count_inputs_as::<divan::counter::ItemsCount>()
            .bench_local_values(|parse_count| {
                parser
                    .parse_input("")
                    .take(parse_count)
                    .for_each(divan::black_box_drop);
            });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn reusable_parser_old_api_100_inputs(bencher: divan::Bencher) {
        let polish_calc_grammar: bnf::Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
        .parse()
        .unwrap();

        // Old API: parse each input (grammar.parse_input does internal setup each time)
        bencher
            .with_inputs(|| {
                let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
                (0..100)
                    .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
                    .collect::<Vec<_>>()
            })
            .bench_local_refs(|inputs| {
                for input in inputs {
                    polish_calc_grammar
                        .parse_input(input)
                        .for_each(divan::black_box_drop);
                }
            });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn reusable_parser_new_api_100_inputs(bencher: divan::Bencher) {
        let polish_calc_grammar: bnf::Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
        .parse()
        .unwrap();

        // New API: construct parser once, parse 100 inputs
        let parser = polish_calc_grammar.build_parser().unwrap();
        bencher
            .with_inputs(|| {
                let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
                (0..100)
                    .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
                    .collect::<Vec<_>>()
            })
            .bench_local_refs(|inputs| {
                for input in inputs {
                    parser.parse_input(input).for_each(divan::black_box_drop);
                }
            });
    }
}
