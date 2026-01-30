# Benchmarking

Benchmarking numbers will vary across tests, specific grammars, rust versions, and hardware. With so many sources of noise, it is important to remember that "faster" is not always easy to define.

With that in mind, BNF's benchmarking has the following goals:

* identify statistically significant performance regressions
* validate performance hypothesis

These benchmarks are not run during continuous integration testing. But if a developer is attempting a full overhaul of the BNF parser, these benchmarks will help them identify large changes in performance.

## Benchmarking Framework

BNF uses the [Divan][divan] benchmarking framework to provide insights into performance, particularly around memory allocation and throughput.

## How to Run

For Divan benchmarks:
> cargo bench --bench divan

## Flamegraph

> CARGO_PROFILE_BENCH_DEBUG=true cargo flamegraph --bench divan -- --bench

`sudo` may be required for `dtrace` on macOS

## Tracing

BNF has an optional "tracing" feature which will provide tracing spans during benchmarking.

The benchmarks are enabled to write these tracing spans to `tracing.folded`. This data can then be parsed to provide a flamegraph.

[divan]: https://crates.io/crates/divan
