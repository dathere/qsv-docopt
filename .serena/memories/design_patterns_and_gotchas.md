# Design Patterns & Gotchas

## Usage string IS the grammar
Every docopt program's parser is derived at runtime from a `&str` usage block. There is no separate schema. `src/parse.rs` is the engine that turns that string into a `Pattern` tree of `Atom`s. Any change in parse.rs potentially changes the semantics of *every* downstream user's usage string — tread carefully and lean on the generated `testcases.rs` fixtures.

## Two result APIs, one error
- Untyped: `.parse()` → `ArgvMap` (good for dynamic access; requires manual conversion).
- Typed: `.deserialize()` → `T: Deserialize` (does conversion + validation; preferred in qsv itself).
Both return the same `Error` and share the `.unwrap_or_else(|e| e.exit())` exit idiom.

## Field-name prefixes are silent
`#[derive(Deserialize)]` fields must be named `flag_*`, `arg_*`, `cmd_*` to match usage-string tokens. A typo yields default values at runtime — no compile error, no runtime warning. When writing tests or examples, double-check the prefix.

## Lossy-UTF-8 argv
`std::env::args_os()` is read internally with lossy conversion: invalid bytes → U+FFFD instead of a panic. Consumers that truly need byte-exact argv must bypass this by constructing the vector themselves and passing it to `.argv(...)`.

## Option synonyms via `SynonymMap`
`-a` and `--archive` are stored once, keyed by both spellings. `get_bool("-a")` and `get_bool("--archive")` must return the same thing. When adding features that iterate keys, iterate via the synonym map's primary-key view to avoid double-counting.

## `ahash` everywhere
The crate deliberately uses `ahash::AHashMap` rather than `std::collections::HashMap` (faster, non-random hashing, works well for small string keys). New code should follow suit.

## Generated testcases.rs
`src/test/testcases.rs` is a checked-in artifact produced by `scripts/mk-testcases` from `src/test/testcases.docopt`. CI doesn't regenerate it, so:
- **Never** hand-edit `testcases.rs`.
- After editing `testcases.docopt`, regenerate and commit both.
- If a test seems to be testing stale behavior, check the commit log for a missing regen.

## Nightly-only formatting
`rustfmt.toml` uses features only nightly rustfmt supports (`wrap_comments`, `format_strings`, `group_imports`, `imports_granularity`, alignment thresholds). Always format with `cargo +nightly fmt`; stable silently ignores those options and produces a different layout.

## No lint/format CI gate
`.github/workflows/*.yml` only build and test. Contributors are responsible for formatting and clippy hygiene locally.
