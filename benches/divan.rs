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
            #[cfg(feature = "tracing")]
            let _span = tracing::span!(tracing::Level::DEBUG, "bench_parse_postal").entered();
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
            #[cfg(feature = "tracing")]
            let _span = tracing::span!(tracing::Level::DEBUG, "bench_parse_postal_input").entered();
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
                #[cfg(feature = "tracing")]
                let _span = tracing::span!(tracing::Level::DEBUG, "bench_generate_dna").entered();
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
            #[cfg(feature = "tracing")]
            let _span =
                tracing::span!(tracing::Level::DEBUG, "bench_parse_polish_calculator").entered();
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
                #[cfg(feature = "tracing")]
                let _span = tracing::span!(
                    tracing::Level::DEBUG,
                    "bench_parse_infinite_nullable_grammar"
                )
                .entered();
                infinite_grammar
                    .parse_input("")
                    .take(parse_count)
                    .for_each(divan::black_box_drop);
            });
    }
}

mod generation_strategies {
    use bnf::{CoverageGuided, DepthBounded, RandomWalk, Weighted};

    const SEED: [u8; 32] = [0; 32];

    fn postal_grammar() -> bnf::Grammar {
        include_str!("../tests/fixtures/postal_address.terminated.input.bnf")
            .parse()
            .unwrap()
    }

    #[divan::bench(min_time = 5, max_time = 30)]
    fn generate_random_walk(bencher: divan::Bencher) {
        bencher.with_inputs(postal_grammar).bench_refs(|grammar| {
            let mut strategy = RandomWalk::from_seed(SEED);
            grammar
                .generate_seeded_with_strategy(&mut strategy)
                .unwrap()
        });
    }

    #[divan::bench(min_time = 5, max_time = 30)]
    fn generate_depth_bounded(bencher: divan::Bencher) {
        bencher.with_inputs(postal_grammar).bench_refs(|grammar| {
            let mut strategy = DepthBounded::from_seed(10, SEED);
            grammar
                .generate_seeded_with_strategy(&mut strategy)
                .unwrap()
        });
    }

    #[divan::bench(min_time = 5, max_time = 30)]
    fn generate_coverage_guided(bencher: divan::Bencher) {
        bencher.with_inputs(postal_grammar).bench_refs(|grammar| {
            let mut strategy = CoverageGuided::from_seed(SEED);
            grammar
                .generate_seeded_with_strategy(&mut strategy)
                .unwrap()
        });
    }

    #[divan::bench(min_time = 5, max_time = 30)]
    fn generate_weighted(bencher: divan::Bencher) {
        bencher.with_inputs(postal_grammar).bench_refs(|grammar| {
            let mut strategy = Weighted::from_seed(100, 1, SEED);
            grammar
                .generate_seeded_with_strategy(&mut strategy)
                .unwrap()
        });
    }
}

mod parser_api {
    #[divan::bench(min_time = 5, max_time = 60)]
    fn build_postal_parser(bencher: divan::Bencher) {
        let grammar = divan::black_box(
            include_str!("../tests/fixtures/postal_address.terminated.input.bnf")
                .parse::<bnf::Grammar>()
                .unwrap(),
        );

        bencher.bench(|| {
            #[cfg(feature = "tracing")]
            let _span =
                tracing::span!(tracing::Level::DEBUG, "bench_build_postal_parser").entered();
            grammar.build_parser().unwrap();
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn build_polish_parser(bencher: divan::Bencher) {
        let grammar = divan::black_box(
            "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
            .parse::<bnf::Grammar>()
            .unwrap(),
        );

        bencher.bench(|| {
            #[cfg(feature = "tracing")]
            let _span =
                tracing::span!(tracing::Level::DEBUG, "bench_build_polish_parser").entered();
            grammar.build_parser().unwrap();
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_postal_with_parser(bencher: divan::Bencher) {
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
            #[cfg(feature = "tracing")]
            let _span =
                tracing::span!(tracing::Level::DEBUG, "bench_parse_postal_with_parser").entered();
            let index = index.next().unwrap();
            let input = random_postal_strings.get(index).unwrap();
            parser.parse_input(input).for_each(divan::black_box_drop);
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_polish_with_parser(bencher: divan::Bencher) {
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
            #[cfg(feature = "tracing")]
            let _span =
                tracing::span!(tracing::Level::DEBUG, "bench_parse_polish_with_parser").entered();
            let index = index.next().unwrap();
            let input = random_walks.get(index).unwrap();
            parser.parse_input(input).for_each(divan::black_box_drop);
        });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn parse_infinite_nullable_with_parser(bencher: divan::Bencher) {
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
                #[cfg(feature = "tracing")]
                let _span = tracing::span!(
                    tracing::Level::DEBUG,
                    "bench_parse_infinite_nullable_with_parser"
                )
                .entered();
                parser
                    .parse_input("")
                    .take(parse_count)
                    .for_each(divan::black_box_drop);
            });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn per_input_100(bencher: divan::Bencher) {
        let polish_calc_grammar: bnf::Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
        .parse()
        .unwrap();

        // One-time parser: parse each input (grammar.parse_input does internal setup each time)
        bencher
            .with_inputs(|| {
                let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
                (0..100)
                    .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
                    .collect::<Vec<_>>()
            })
            .bench_local_refs(|inputs| {
                #[cfg(feature = "tracing")]
                let _span = tracing::span!(tracing::Level::DEBUG, "bench_per_input_100").entered();
                for input in inputs {
                    polish_calc_grammar
                        .parse_input(input)
                        .for_each(divan::black_box_drop);
                }
            });
    }

    #[divan::bench(min_time = 5, max_time = 60)]
    fn reuse_parser_100(bencher: divan::Bencher) {
        let polish_calc_grammar: bnf::Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= '+' | '-' | '*' | '/'
            <number> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
        "
        .parse()
        .unwrap();

        // Reusable parser: construct parser once, parse 100 inputs
        let parser = polish_calc_grammar.build_parser().unwrap();
        bencher
            .with_inputs(|| {
                let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
                (0..100)
                    .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
                    .collect::<Vec<_>>()
            })
            .bench_local_refs(|inputs| {
                #[cfg(feature = "tracing")]
                let _span =
                    tracing::span!(tracing::Level::DEBUG, "bench_reuse_parser_100").entered();
                for input in inputs {
                    parser.parse_input(input).for_each(divan::black_box_drop);
                }
            });
    }
}
