# Contributing to bnf

:wave: welcome! And thanks for taking time to contribute!


## Code of Conduct

This project and everyone participating in it is governed by the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold this code. Please report unacceptable behavior to [bnf@shnewto.dev](mailto:bnf@shnewto.dev).


## Questions

Please feel free to raise issues to ask questions or report bugs. If you'd like to open a PR but want to touch bases first, feel free to raise an issue then too.

## Opening PRs

Good PR comments go a long way. It means a lot (and really helps) when you take the time to explain _why_ your PR is doing what it does.

## Mutation testing

We use [cargo-mutants](https://crates.io/crates/cargo-mutants) to find gaps in the test suite (code that runs but isn’t asserted on). Optional, not required for PRs.

- **Install:** `cargo install cargo-mutants`
- **Run:** `cargo mutants` (or `cargo mutants --all-features`). Use `-f 'src/foo.rs'` to limit scope, `--list` to see mutants without running tests.
- **Results:** *missed* = mutation not caught by any test (add a test or `#[mutants::skip]`); *caught* = good; *unviable* = didn’t compile; *timeout* = add `#[mutants::skip]` to that function.


Thanks again!
