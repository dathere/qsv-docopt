# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project purpose

`qsv_docopt` is a fork of the unmaintained [docopt.rs](https://github.com/docopt/docopt.rs), maintained for the [qsv](https://github.com/jqnatividad/qsv) CLI. Docopt derives the argument parser from the self-documenting usage string, which is what qsv relies on and which `clap`/`structopt` cannot replicate. The crate ships a library (`qsv_docopt`) and a small binary (`docopt-wordlist`, `src/wordlist.rs`) used for bash tab-completion.

## Commands

```bash
cargo build              # debug build
cargo build --release
cargo test               # full suite, including generated testcases
cargo test <substring>   # run a single test by name substring

# Formatting requires nightly — rustfmt.toml uses nightly-only options
# (wrap_comments, format_strings, group_imports, imports_granularity,
# *_align_threshold). Stable `cargo fmt` will not apply project style.
cargo +nightly fmt

# Regenerate src/test/testcases.rs after editing src/test/testcases.docopt.
# testcases.rs is a checked-in generated artifact; CI does not regenerate it,
# so a stale .rs silently tests the old fixtures.
./scripts/mk-testcases ./src/test/testcases.docopt > ./src/test/testcases.rs
# or: make src/test/testcases.rs
```

MSRV: Rust 1.95, edition 2024 (see `Cargo.toml`). CI (`.github/workflows/{linux,macos,windows}.yml`) only runs `cargo build --verbose` and `cargo test --verbose` — there is no lint or format gate.

## Architecture

- `src/lib.rs` — crate entry, module declarations, crate-level doc examples.
- `src/dopt.rs` — public API surface. `Docopt` builder (`new` → `argv` → `parse`/`deserialize`), `ArgvMap` (untyped result, accessed with `get_bool` / `get_count` / `get_str` / `get_vec`), `Value` (`Switch` / `Counted` / `Plain` / `List`), `Error`, and the serde `Deserializer` impl that powers typed `.deserialize()`.
- `src/parse.rs` — docopt grammar. `Parser` builds a `Pattern` tree of `Atom`s from the usage string; `Matcher` + `MState` walk an `Argv` stream against that tree. Edits here change how all usage strings are interpreted.
- `src/synonym.rs` — `SynonymMap` backs option synonyms (e.g. `-a` ↔ `--archive`) so lookups by either spelling resolve to the same value. The crate uses `ahash::AHashMap` throughout; follow suit rather than reaching for `std::collections::HashMap`.
- `src/utils.rs` — shared helpers.
- `src/wordlist.rs` — the `docopt-wordlist` binary.
- `src/test/` — `mod.rs` plus `suggestions.rs` hold hand-written tests; `testcases.docopt` is the fixture source and `testcases.rs` is its generated companion (do not hand-edit).

## Non-obvious conventions

- **Struct field naming for `#[derive(Deserialize)]` targets.** `--flag` / `-f` → `flag_flag`; `<arg>` or `ARG` → `arg_arg` / `arg_ARG`; a bare command token `build` → `cmd_build`. Getting the prefix wrong yields a silent field-miss at runtime, not a compile error.
- **Argument ingestion is lossy-UTF-8.** The crate reads `std::env::args_os()` and replaces non-UTF-8 bytes with U+FFFD instead of panicking. Callers that need byte-exact argv must build the vector themselves and pass it via `.argv(...)`.
- **Two parallel result APIs.** `.parse()` returns an untyped `ArgvMap`; `.deserialize()` returns a user struct via serde. Both share the `Error` type and the `.unwrap_or_else(|e| e.exit())` exit idiom. Match whichever style the surrounding code and tests already use.
