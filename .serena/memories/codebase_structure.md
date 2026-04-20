# Codebase Structure

## Top level
```
Cargo.toml          — manifest (lib + docopt-wordlist bin)
Cargo.lock
Makefile            — legacy targets (docs publish, ctags, push, mk-testcases)
rustfmt.toml        — nightly-only formatter config
scripts/mk-testcases — shell script: src/test/testcases.docopt → testcases.rs
completions/        — shell completion snippets (bash only today)
examples/           — runnable example binaries (cp, cargo, decode, hashmap, …)
src/                — crate sources
.github/workflows/  — linux.yml, macos.yml, windows.yml (build + test only)
```

## `src/` modules (from `src/lib.rs`: `utils`, `dopt`, `parse`, `synonym`, `test`)

### `src/dopt.rs` — public API
- `struct Docopt` — builder. Methods: `new`, `argv`, `parse`, `deserialize`, plus configuration setters (`options_first`, `help`, `version`, etc.).
- `struct ArgvMap` — untyped parse result. Accessors: `get_bool`, `get_count`, `get_str`, `get_vec`, `find`.
- `enum Value` — `Switch(bool)`, `Counted(u64)`, `Plain(Option<String>)`, `List(Vec<String>)`.
- `enum Error` — with `impl fmt::Display`, `impl StdError`, `impl de::Error`, and `exit()` method.
- `Deserializer`, `SeqDeserializer`, `StructDeserializer` — serde impls that power typed `.deserialize()`.
- Free functions: `derr`, `deserialize_num`.

### `src/parse.rs` — docopt grammar engine
- `struct Parser` + `impl Parser` — parses the usage string into a pattern tree.
- `struct PatParser` — pattern sub-parser.
- `enum Pattern`, `enum Atom` — the parsed tree of alternatives / sequences / options / arguments / commands.
- `enum Argument`, `struct Options`, `struct Argv`, `struct ArgvToken` — argv tokenization.
- `struct Matcher`, `struct MState` — matches an `Argv` stream against the `Pattern` tree.
- Helpers: `err`, `parse_long_equal`, `parse_long_equal_argv`, `pattern_tokens`.
- This is the module where changes affect how *every* usage string is interpreted.

### `src/synonym.rs`
- `struct SynonymMap<K, V>` over `ahash::AHashMap` — backs option synonyms (`-a` ↔ `--archive`) so lookups by either spelling resolve to the same value.

### `src/utils.rs`
- Small shared helpers.

### `src/wordlist.rs`
- The `docopt-wordlist` binary (bash tab-completion helper). Builds as a bin target; not part of the library surface.

### `src/test/`
- `mod.rs` — hand-written tests + `test_expect!` / `test_user_error!` macros.
- `suggestions.rs` — tests for the "did-you-mean" (`strsim`) suggestions feature.
- `testcases.docopt` — fixture **source** (human-edited).
- `testcases.rs` — **generated** companion; do not hand-edit.

## Examples (`examples/`)
Each file is a self-contained demo of one feature:
- `cp.rs` — canonical example from the README.
- `cargo.rs` — Cargo-style subcommands.
- `decode.rs` — typed decoding.
- `hashmap.rs` — untyped ArgvMap access.
- `optional_command.rs`, `options_from_usage.rs`, `verbose_multiple.rs` — edge cases.
