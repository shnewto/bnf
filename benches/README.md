# Benchmarking

Benchmarking numbers will vary across tests, specific grammars, rust versions, and hardware. With so many sources of noise, it is important to remember that "faster" is not always easy to define.

With that in mind, BNF's benchmarking has the following goals:

* identify statistically significant performance regressions
* validate performance hypothesis

These benchmarks are not run during continuous integration testing. But if a developer is attempting a full overhaul of the BNF parser, these benchmarks will help them identify large changes in performance.

## Benchmarking Frameworks

BNF uses two benchmarking frameworks to provide different perspectives on performance:

### Criterion

[Criterion][criterion] is used to run benchmarks with confidence. Criterion achieves this by running warmups, collecting a statistically significant sized sample, and generating informative reports.

### Divan

[Divan][divan] provides additional insights into performance, particularly around memory allocation and throughput. It offers a different perspective on performance analysis compared to Criterion.

## How to Run

For Criterion benchmarks:
> cargo criterion

For Divan benchmarks:
> cargo bench --bench divan

## Cargo Criterion

[cargo-criterion][cargo-criterion] is a plugin for Cargo which handles much of the heavy lifting for analyzing and reporting on Criterion-rs benchmarks. It eases generating performance report files.

### Install

> cargo install cargo-criterion

## Flamegraph

Generate flamegraphs for either framework:

For Criterion:
> CARGO_PROFILE_BENCH_DEBUG=true cargo flamegraph --bench criterion -- --bench

For Divan:
> CARGO_PROFILE_BENCH_DEBUG=true cargo flamegraph --bench divan -- --bench

`sudo` may be required for `dtrace` on macOS

## Tracing

BNF has an optional "tracing" feature which will provide tracing spans during benchmarking.

The benchmarks are enabled to write these tracing spans to `tracing.folded`. This data can then be parsed to provide a flamegraph:

> RUST_LOG=DEBUG cargo criterion --features "tracing" && cat tracing.folded | inferno-flamegraph > flamegraph.svg

[criterion]: https://crates.io/crates/criterion
[cargo-criterion]: https://github.com/bheisler/cargo-criterion
[divan]: https://crates.io/crates/divan
