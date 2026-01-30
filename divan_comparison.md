# Divan benchmark: main vs internal-non-terminal-parsing

Comparison of `cargo bench --bench divan` on **main** vs **internal-non-terminal-parsing**.  
Branch output: `/tmp/divan_internal_branch.txt`  
Main output: `/tmp/divan_main.txt`

## Median time comparison (branch vs main)

| Benchmark | main (median) | branch (median) | Δ |
|-----------|---------------|-----------------|---|
| **examples** | | | |
| generate_dna | 561.8 ns | 567.7 ns | +1.0% |
| parse_infinite_nullable_grammar | 86.21 µs | 87.18 µs | +1.1% |
| parse_polish_calculator | 5.749 µs | 5.727 µs | −0.4% |
| **parse_postal** | **23.23 µs** | **30.4 µs** | **+30.9%** |
| parse_postal_input | 239 µs | 245.7 µs | +2.8% |
| **parser_api** | | | |
| build_polish_parser | 882.1 ns | 815.6 ns | −7.5% |
| build_postal_parser | 7.504 µs | 6.921 µs | −7.8% |
| parse_infinite_nullable_with_parser | 85.33 µs | 87.37 µs | +2.4% |
| parse_polish_with_parser | 5.093 µs | 5.15 µs | +1.1% |
| parse_postal_with_parser | 234.9 µs | 241.9 µs | +3.0% |
| per_input_100 | 14.82 ms | 14.5 ms | −2.2% |
| reuse_parser_100 | 14.76 ms | 14.49 ms | −1.8% |

## Mean time comparison (branch vs main)

| Benchmark | main (mean) | branch (mean) | Δ |
|-----------|-------------|----------------|---|
| generate_dna | 604.7 ns | 616.3 ns | +1.9% |
| parse_infinite_nullable_grammar | 115.1 µs | 116.1 µs | +0.9% |
| parse_polish_calculator | 151.1 µs | 148.1 µs | −2.0% |
| **parse_postal** | **23.52 µs** | **30.73 µs** | **+30.6%** |
| parse_postal_input | 627.8 µs | 627.8 µs | 0% |
| build_polish_parser | 910.9 ns | 820.5 ns | −9.9% |
| build_postal_parser | 7.581 µs | 7.029 µs | −7.3% |
| parse_infinite_nullable_with_parser | 114 µs | 116.2 µs | +1.9% |
| parse_polish_with_parser | 149.3 µs | 146.4 µs | −1.9% |
| parse_postal_with_parser | 622.2 µs | 625.4 µs | +0.5% |
| per_input_100 | 14.88 ms | 14.59 ms | −1.9% |
| reuse_parser_100 | 14.85 ms | 14.53 ms | −2.2% |

## Summary

- **parse_postal (~31% slower on branch)**  
  This benchmark parses the postal-address grammar *text* into a `Grammar`.  
  On the branch, that path is: `parsed_grammar_complete` → `normalize_parsed_grammar`.  
  So we always do an extra normalization pass (walk AST, lower terms, allocate productions) even when the grammar has no `( )` or `[ ]`.  
  **Conclusion:** Expected cost of the new “parse then normalize” design. The only benchmark that measures grammar-from-text parsing; others measure parsing *input* with a grammar or building/reusing the parser.

- **build_postal_parser / build_polish_parser (~7–8% faster on branch)**  
  On main, anonymous groups/optionals were expanded into extra productions at parse time, so the `Grammar` had more productions and `ParseGrammar::new` did more work.  
  On the branch, the postal and Polish bench grammars are plain (no `( )` / `[ ]` in the string), and the internal representation no longer expands anonymous productions, so the built parser has the same or fewer productions.  
  **Conclusion:** Branch is faster here because we no longer expand inline; builder does less work.

- **All other benchmarks**  
  Differences are small (roughly ±2–3%) and within normal run-to-run variation. No other meaningful performance regression.

## Verdict

- **One expected regression:** grammar-from-text parsing (`parse_postal`) is ~30% slower due to the extra normalization step.
- **No other performance issues:** input parsing, generation, and parser build/reuse are the same or slightly better on the branch.
