# Using tracing spans to optimize benchmarks

This document gives step-by-step instructions for using the crate’s tracing spans to find and optimize hot paths. It is aimed at an agent or developer doing performance work.

## 1. What is instrumented

Tracing is gated by the `tracing` feature. When enabled with `RUST_LOG=debug`, the following code paths emit spans:

| Benchmark(s) | What they exercise | Spans you will see |
|--------------|--------------------|--------------------|
| **parse_postal** | Parse grammar *text* into a `Grammar` | `Grammar::parse_from`, `grammar_fast_path` or `grammar_extended_path`, `grammar_complete`, `grammar`, `production`, `prod_lhs`, `prod_rhs`, `expression`, `term`, `terminal`, `nonterminal`, `whitespace_plus_comments`. If extended syntax is used: `normalize_parsed_grammar`, `lower_expression`, `lower_term`. |
| **parse_postal_input**, **parse_polish_calculator**, **parse_*_with_parser**, **parse_infinite_nullable_***, **per_input_100**, **reuse_parser_100** | Parse *input strings* with a grammar (Earley) | `parse_starting_with_grammar`, `earley`, `Predict`, `Scan`, `Complete`, `insert`, `get_complete`, `get_incomplete`, `next_parse_tree`, `ParseGrammar_new`, and traversal: `match_iter_new`, `match_iter_next`, `match_term`, `traversal_tree_predict_is_starting`. |
| **build_postal_parser**, **build_polish_parser** | Build a reusable parser from a grammar | `GrammarParser::new`, `validate_nonterminals`, `ParseGrammar_new`. |
| **generate_dna** | Generate a random sentence from a grammar | `generate_seeded_callback`, `traverse`, `eval_terminal`. |

Span names in the trace are like `bnf::parsers::grammar_complete:src/parsers/mod.rs:252` (module path and line). The **text summary** aggregates by the full span name; the **flamegraph** shows the call hierarchy.

## 2. Run a traced benchmark and get a summary

Do this for **one** benchmark at a time so the trace stays manageable and the summary is interpretable.

1. **Run that benchmark with tracing** (replace `BENCH_NAME` with the exact benchmark name, e.g. `parse_postal`, `generate_dna`, `parse_postal_input`, `build_postal_parser`):

   ```bash
   RUST_LOG=debug cargo bench --bench divan --features tracing BENCH_NAME
   ```

   This writes `tracing.folded` in the **package root** (directory that contains `Cargo.toml`).

2. **Produce a text summary** (recommended: easy to read and reason about):

   ```bash
   head -n 100000 tracing.folded | cargo run --bin summarize_trace
   ```

   The summarizer reads folded lines from stdin and prints a table: span name, total samples, and percentage of total. Use a prefix (e.g. 100k lines) so the file is small and the summary is still representative.

3. **Optional: flamegraph** (visual, good for call stacks):

   ```bash
   head -n 100000 tracing.folded | inferno-flamegraph > flamegraph.svg
   ```

   Open `flamegraph.svg` in a browser. Install inferno with `cargo install inferno` if needed.

## 3. Map summary output back to code

- **SPAN** column: full span name, often including path and line, e.g. `bnf::parsers::prod_rhs:src/parsers/mod.rs:120`.
- **SAMPLES** / **%**: inclusive time: that span plus everything it calls. Higher % = better optimization target.
- **Where to edit**: use the path and line (e.g. `src/parsers/mod.rs` around line 120) to find the function. The span is created at the **start** of that function (look for `span!(..., "name").entered()` or `crate::tracing::span!(...).entered()`).

Focus first on spans that:

- Have high **%** (e.g. top 5–10 in the table).
- Are in code paths you can change (e.g. hot parsers, loops, allocation sites).

## 4. Optimization strategies by hotspot

Use the table below only **after** you have run the summarizer for the benchmark you care about. The “likely hotspots” are the spans that often show up at the top; your trace may differ.

| If the summary is dominated by… | Likely benchmark | What to try |
|--------------------------------|------------------|-------------|
| **grammar_complete**, **grammar**, **production**, **prod_rhs**, **expression**, **term**, **terminal**, **nonterminal**, **whitespace_plus_comments** | parse_postal | Optimize the **grammar-text** parsing path in `src/parsers/mod.rs`: fewer allocations, faster whitespace/comments, `#[inline(always)]` on hot parsers, pre-allocated lists (e.g. in `xt_list_with_separator`). |
| **normalize_parsed_grammar**, **lower_expression**, **lower_term** | Parse of grammar that uses `( )` or `[ ]` | Optimize **normalization** in `src/parsers/mod.rs`: less cloning, smaller allocations, or avoiding work when the parsed term is already Terminal/Nonterminal. |
| **earley**, **Predict**, **Scan**, **Complete**, **insert**, **get_complete**, **get_incomplete** | parse_postal_input, parse_*_with_parser, etc. | Optimize the **Earley** path in `src/earley/mod.rs`: data structures for the queue/completions, reducing work per prediction/scan/complete, or allocation in hot loops. |
| **match_term**, **match_iter_next**, **traversal_tree_predict_is_starting** | Same as above | Optimize **traversal** in `src/earley/traversal.rs`: matching and tree updates. |
| **ParseGrammar_new** | build_*_parser or first parse | Optimize **parser build** in `src/parser/grammar.rs` and/or `src/earley/grammar.rs`: how productions are flattened and indexed. |
| **validate_nonterminals** | build_*_parser | Optimize **validation** in `src/parser/mod.rs`: fewer passes or less allocation when collecting defined/referenced nonterminals. |
| **generate_seeded_callback**, **traverse**, **eval_terminal** | generate_dna | Optimize **generation** in `src/grammar.rs`: finding productions (e.g. avoid repeated linear search), string building, or RNG usage. |

Do **one** change at a time, then re-run the same benchmark (with and without tracing) to confirm improvement and that the trace still makes sense.

## 5. Verify an optimization

1. **Run the same benchmark without tracing** (so tracing overhead doesn’t skew numbers):

   ```bash
   cargo bench --bench divan BENCH_NAME
   ```

2. Compare **median** (and optionally mean) from the Divan output before vs after your change. Keep the benchmark name and command identical.

3. **Re-run tests** to ensure behavior is unchanged:

   ```bash
   cargo test
   ```

4. If you added or changed tracing spans, run the traced benchmark again and confirm the summary still reflects the code path you optimized.

## 6. Quick reference: commands

```bash
# Single benchmark with tracing (smaller trace)
RUST_LOG=debug cargo bench --bench divan --features tracing parse_postal

# Text summary (run from package root)
head -n 100000 tracing.folded | cargo run --bin summarize_trace

# Flamegraph
head -n 100000 tracing.folded | inferno-flamegraph > flamegraph.svg

# Same benchmark without tracing (timing only)
cargo bench --bench divan parse_postal
```

Replace `parse_postal` with the benchmark you are optimizing (e.g. `generate_dna`, `parse_postal_input`, `build_postal_parser`).

## 7. File locations

- **Bench definitions**: `benches/divan.rs`
- **Grammar-from-text parsing**: `src/parsers/mod.rs` (e.g. `grammar_complete`, `production`, `prod_rhs`, `expression`, `term`, `terminal`, `nonterminal`, `whitespace_plus_comments`, `normalize_parsed_grammar`, `lower_expression`, `lower_term`)
- **Grammar entry**: `src/grammar.rs` (`Grammar::parse_from`, `generate_seeded_callback`, `traverse`, `eval_terminal`)
- **Parser build / validation**: `src/parser/mod.rs` (`GrammarParser::new`, `validate_nonterminals`)
- **Parse grammar construction**: `src/parser/grammar.rs`, `src/earley/grammar.rs` (`ParseGrammar::new`)
- **Earley and traversal**: `src/earley/mod.rs`, `src/earley/traversal.rs`
- **Trace summarizer**: `src/bin/summarize_trace.rs`
- **Benchmarking overview**: `benches/README.md`

Use this flow: pick a benchmark → run it with tracing → summarize (and optionally flamegraph) → find high-% spans → map to the files above → apply and verify one optimization at a time.
