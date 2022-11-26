use bnf::Grammar;
use criterion::{criterion_group, criterion_main, Criterion};
use rand::seq::SliceRandom;

#[cfg(feature = "tracing")]
fn init_tracing() -> impl Drop {
    use tracing_flame::FlameLayer;
    use tracing_subscriber::{fmt, prelude::*};
    let fmt_layer = fmt::Layer::default();

    let (flame_layer, _guard) = FlameLayer::with_file("./tracing.folded").unwrap();

    tracing_subscriber::registry()
        .with(fmt_layer)
        .with(flame_layer)
        .init();

    _guard
}

#[cfg(not(feature = "tracing"))]
fn init_tracing() {}

fn examples(c: &mut Criterion) {
    // c.bench_function("parse postal", |b| {
    //     let input = std::include_str!("../tests/fixtures/postal_address.terminated.input.bnf");
    //     b.iter(|| input.parse::<Grammar>().unwrap());
    // });

    // c.bench_function("generate DNA", |b| {
    //     let input = "<dna> ::= <base> | <base> <dna>
    //         <base> ::= \"A\" | \"C\" | \"G\" | \"T\"";
    //     let grammar: Grammar = input.parse().unwrap();
    //     b.iter(|| grammar.generate().unwrap());
    // });

    let _tracing = init_tracing();

    let polish_calc_grammar: Grammar = "<product> ::= <number> | <op> <product> <product>
            <op> ::= \"+\" | \"-\" | \"*\" | \"/\"
            <number> ::= \"0\" | \"1\" | \"2\" | \"3\" | \"4\" | \"5\" | \"6\" | \"7\" | \"8\" | \"9\"
        ".parse().unwrap();

    // use pseudo random for consistent metrics
    let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(0);
    let random_walk_count = 100usize;
    let random_walks: Vec<_> = (0..random_walk_count)
        .map(|_| polish_calc_grammar.generate_seeded(&mut rng).unwrap())
        .collect();

    #[cfg(feature = "tracing")]
    let _span = tracing::span!(tracing::Level::TRACE, "BENCH ITER").entered();

    c.bench_function("parse polish calculator", |b| {
        b.iter(|| {
            let input = random_walks.choose(&mut rng).unwrap();
            let _: Vec<_> = polish_calc_grammar.parse_input(input).collect();
        })
    });

    // c.bench_function("reuse polish calculator parser", |b| {
    //     let parser = polish_calc_grammar.parser();
    //     b.iter(|| {
    //         let input = random_walks.choose(&mut rng).unwrap();
    //         let _: Vec<_> = parser.parse(input).collect();
    //     })
    // });
}

criterion_group!(benches, examples);
criterion_main!(benches);
