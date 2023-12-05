fn main() {
    init_tracing();

    #[cfg(feature = "tracing")]
    let _span = tracing::span!(tracing::Level::DEBUG, "BENCH EXAMPLES").entered();

    // Run registered benchmarks.
    divan::main();
}

#[cfg(feature = "tracing")]
fn init_tracing() -> impl Drop {
    use tracing_flame::FlameLayer;
    use tracing_subscriber::{fmt, prelude::*};
    let filter_layer = tracing_subscriber::EnvFilter::from_default_env();
    let fmt_layer = fmt::Layer::default();
    let (flame_layer, _guard) = FlameLayer::with_file("./tracing.folded").unwrap();

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .with(flame_layer)
        .init();

    _guard
}

#[cfg(not(feature = "tracing"))]
fn init_tracing() {}

mod examples {
    #[divan::bench]
    fn parse_postal(bencher: divan::Bencher) {
        let input = divan::black_box(include_str!(
            "../tests/fixtures/postal_address.terminated.input.bnf"
        ));

        bencher.bench(|| {
            input.parse::<bnf::Grammar>().unwrap();
        });
    }

    #[divan::bench]
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

    #[divan::bench]
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
        let mut random_walks = divan::black_box(random_walks.into_iter());

        bencher.bench_local(|| {
            let input = random_walks.next().unwrap();
            polish_calc_grammar.parse_input(&input).for_each(|v| _ = divan::black_box(v));
        });
    }

    #[divan::bench]
    fn parse_infinite_nullable_grammar(bencher: divan::Bencher) {
        use rand::Rng;

        let infinite_grammar: bnf::Grammar = "
                <a> ::= '' | <b>
                <b> ::= <a>"
            .parse()
            .unwrap();

        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);

        bencher
            .with_inputs(|| rng.gen_range(1..100))
            .count_inputs_as::<divan::counter::ItemsCount>()
            .bench_local_values(|parse_count| {
            infinite_grammar.parse_input("").take(parse_count).for_each(|v| _ = divan::black_box(v));
            });
    }
}
