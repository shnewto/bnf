# Compile-time BNF parsing: research and recommendation

## Problem

Users with a fixed grammar want to avoid shipping the full BNF parser at runtime. Today:

- `Grammar::from_str()` / `.parse()` uses nom and runs at runtime.
- `FromStr` is not `const`, so BNF text cannot be parsed in `const` context.
- Even with `const BNF: &str = include_str!("grammar.bnf")`, parsing still happens at runtime (e.g. via `LazyLock`), and the nom-based parser remains in the binary.

## Goal

Parse BNF at compile time so that:

1. The BNF parser (nom, etc.) is not required in the compiled application.
2. Grammar construction for constant grammars happens at compile/build time.
3. Users can still write BNF syntax (string or file), not a different DSL.

---

## Option 1: Extend the existing `grammar!` declarative macro

### How it works today

The crate already has a `grammar!` macro that accepts BNF-like token trees:

```rust
bnf::grammar! {
  <dna> ::= <base> | <base> <dna>;
  <base> ::= 'A' | 'C' | 'G' | 'T';
};
```

- Parsing is done by the **macro expander** (at compile time): it matches `<lhs> ::= ... ;` and builds nested `term!`, `Expression::from_parts`, `Production::from_parts`, `Grammar::from_parts`.
- The **resulting code** still runs at runtime: `vec![]`, `.push()`, `stringify!($ident).to_string()`, so the `Grammar` value is built at runtime. The BNF **string** parser (nom) is never used.

### Pros

- No new crates or proc macros.
- BNF parser (nom) is not used for this path; only macro expansion + runtime allocation.
- Already supports a fixed grammar without `FromStr` in the hot path.
- Familiar BNF-like syntax for users who can live within macro token rules.

### Cons

- **Not real BNF text**: nonterminals must be Rust `ident` (e.g. `dna`, `base`), so `<nonterminal-pattern>` is not valid. Terminals are Rust `literal` (string/number). So it’s a BNF-**like** DSL, not “parse this BNF string.”
- **Still runtime allocation**: the macro expands to code that builds `Vec`s and `String`s at runtime. So you avoid the BNF parser but not heap allocation for the grammar.
- **No `include_str!`**: you cannot `grammar!(include_str!("file.bnf"))`; the macro expects token trees, not a single string.

### Possible extensions

- **Const output**: try to have the macro emit `const`-friendly data (e.g. arrays + a `const fn` or a `static` with a getter). That would require either:
  - Grammar types that can be built from fixed-size/const data (e.g. `&[Production]` or const generics), or
  - Keeping current types and accepting that the macro still produces runtime-constructed `Grammar`.
- **Relax ident/literal**: more macro rules for hyphenated “idents” or quoted strings as token sequences; possible but messy and still not arbitrary BNF strings.

### Verdict

Good for “I have a fixed grammar and don’t want to pull in the BNF parser at runtime,” but it does **not** satisfy “parse BNF syntax at compile time” if by that we mean **literal BNF strings** (e.g. from a file or a `r#"..."#` string). It’s one of the three options and the one that already exists.

---

## Option 2: Procedural macro that parses BNF at compile time

### Idea

Introduce a proc macro (e.g. in a `bnf-macros` crate or feature) that takes a **literal BNF string** and runs the **existing** grammar parser at compile time, then emits code that constructs the same `Grammar`.

Example API:

```rust
// From a literal string
const GRAMMAR: Grammar = bnf::const_grammar!(r#"
  <dna> ::= <base> | <base> <dna>
  <base> ::= 'A' | 'C' | 'G' | 'T'
"#);

// From a file
const GRAMMAR: Grammar = bnf::const_grammar!(include_str!("grammar.bnf"));
```

Implementation sketch:

- Proc macro receives a `Literal` (string) or an expression that expands to a string (e.g. `include_str!(...)`).
- In the macro, call the same grammar parser used by `Grammar::parse_from::<BNF>()` (or a minimal copy) on that string.
- If parsing fails, emit a compile_error! with a clear message.
- If it succeeds, emit code that builds the `Grammar`: e.g. `Grammar::from_parts(vec![...])` with `Production::from_parts`, `Expression::from_parts`, `Term::*` filled from the parse result.

Because `Grammar`/`Production`/`Expression`/`Term` use `Vec` and `String`, the emitted code will do runtime allocation. So you get:

- **Compile-time**: BNF string is parsed; only the proc macro (and its dependency on the parser) runs. The **application** crate does not call `FromStr` or the nom parser.
- **Runtime**: a `Grammar` is built once (e.g. when the `static` or `const` is first used, or in a function that returns `Grammar::from_parts(...)`).

So “parse BNF at compile time” is achieved: the parser runs in the compiler/build, not in the final binary. The binary only contains the code that builds the already-parsed structure (vecs and strings).

### Pros

- **Real BNF**: users can paste or `include_str!` standard BNF (with `<nonterminal>`, `::=`, `|`, quoted terminals, etc.).
- **Single source of truth**: the same grammar parser (nom) used for runtime parsing is used by the macro; no second grammar syntax.
- **No BNF parser in the app**: the application binary does not need nom for grammar parsing; only the proc macro crate (build-time) does.
- **Good UX**: `const_grammar!(include_str!("grammar.bnf"))` matches the “constant grammar from a file” use case and keeps BNF in files.

### Cons

- **Proc macro crate**: need a separate crate or feature (e.g. `bnf-macros`) with syn, quote, and a way to call the grammar parser (same crate or dependency). Build and maintenance cost.
- **Const vs static**: today you cannot do `const GRAMMAR: Grammar = ...` with `Grammar::from_parts(vec![...])` on stable Rust (non-empty `Vec` construction is not const). So the macro would typically emit either:
  - A **function** that returns `Grammar` (e.g. `fn grammar() -> Grammar { ... }`), or
  - A **static** with `OnceCell`/`LazyLock` (e.g. `static GRAMMAR: LazyLock<Grammar> = LazyLock::new(|| ...);`).  
  So “const parse” here means “parse at compile time,” not necessarily “store in a `const`” unless you add a separate const-friendly representation later.
- **ABNF**: if you support both BNF and ABNF, the macro might take a format parameter or a second macro (e.g. `const_grammar_abnf!`).

### Verdict

**Best fit for the stated goal**: “Allow BNF syntax to be parsed at compile-time” and “no reason to include an entire BNF parser in the compiled application.” Real BNF strings, parse once at compile time, parser not in the final binary. The main design choice is whether to expose the result as a function, a `LazyLock` static, or (later) a true const representation.

---

## Option 3: Pure `const fn` BNF parser

### Idea

Implement a BNF parser as a **const fn** that takes `&str` and returns something equivalent to `Grammar`, so that `const GRAMMAR: Grammar = parse_bnf!(...);` (or similar) works without proc macros.

### Constraints of const fn (stable Rust)

- No heap allocation: no `Vec::push`, no `String`, no `Box`, etc.
- No trait objects, no non-const fn calls (so no nom, no regex).
- Parsing must be done with only const-compatible operations (e.g. indexing `&str`, loops, conditionals, const-friendly data structures).

So we’d need:

- A parser implemented by hand (e.g. recursive descent or a simple state machine) using only `const fn`-allowed operations.
- A **const-friendly representation** of the grammar: e.g. fixed-capacity arrays (`[Term; N]`, `[Production; M]`) or slices over `'static` data (`&'static [Production]`). That implies:
  - **No `Vec`/`String`** in the core types used in const context; likely `&'static str` (or fixed-size buffers) for symbol names and a different type (e.g. `Grammar<'static>`) for the const grammar.
- Either a fixed maximum size (e.g. max rules, max symbols) or const generics (e.g. `Grammar<const N: usize>`) to size arrays.

### Pros

- No proc macro, no extra crate: just a `const fn` and possibly a small `const_grammar!` macro that calls it.
- True `const` evaluation: grammar is parsed and stored in const data; no lazy initialization.
- Conceptually clean: “parse BNF in const” with no build-time magic.

### Cons

- **Large implementation effort**: reimplement a BNF (and optionally ABNF) parser in const-safe code; no nom, no heap.
- **Type and API impact**: current `Grammar` uses `Vec<Production>`, `Term::Terminal(String)`, etc. To hold the result in const you either:
  - Introduce new types (e.g. `ConstGrammar<'a>`, terms as `&'a str`), and possibly conversion to `Grammar`, or
  - Change existing types to support const construction (e.g. const-collections, or switching to `&'static str` and slice-based storage), which is a breaking change and a big refactor.
- **Limits**: fixed max number of rules/symbols or more complex const-generic designs; no unbounded growth.
- **Maintenance**: two parsers (runtime nom vs const) unless you restrict const to a subset of BNF and accept divergence.

### Verdict

Elegant long-term goal, but **not the best first step**: it requires a second parser, new or heavily refactored types, and significant work. Better as a possible future direction after Option 2 is in place.

---

## Recommendation

**Prefer Option 2 (procedural macro)** to satisfy the feature request:

1. **“BNF parsed at compile time”**: the macro runs the existing BNF grammar parser at compile time on a string (or `include_str!(...)`). No `FromStr` at runtime.
2. **“No BNF parser in the compiled application”**: the application only depends on the proc macro at build time; the emitted code just builds `Grammar` from literal data. The nom-based parser is not linked into the final binary for that use case.
3. **Real BNF**: users keep writing BNF as strings or files, including `<nonterminal>`, `::=`, `|`, quoted terminals, etc., without the limitations of the `grammar!` token-tree DSL.

**Suggested implementation steps**

- Add a `bnf-macros` crate (or a `macros` feature in this repo) with a proc macro, e.g. `const_grammar!(string)` and optionally `const_grammar!(include_str!(...))`.
- In the macro, invoke the existing grammar parser (e.g. `parsers::grammar_complete::<BNF>`) on the string; on success, emit `Grammar::from_parts(vec![...])` (or a helper that returns it); on failure, emit `compile_error!(...)`.
- Document that the result is “grammar parsed at compile time” and that the concrete value can be exposed as a function returning `Grammar` or a `LazyLock<Grammar>` static until/unless a const-compatible representation is added later.

**Option 1 (existing macro)** remains useful for users who are fine with the BNF-like DSL and Rust token rules; it already avoids the BNF parser at runtime and can be documented as the “fixed grammar without runtime parsing” path when BNF string parsing is not required.

**Option 3 (const fn parser)** is a possible follow-up once Option 2 exists, if you want a true `const Grammar` and are willing to invest in const-safe types and a second parser.
