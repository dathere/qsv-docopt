# Code Style & Conventions

## Formatting
- `rustfmt.toml` requires **nightly rustfmt** (`cargo +nightly fmt`). Key settings:
  - `comment_width = 100`, `wrap_comments = true`
  - `format_strings = true`
  - `group_imports = "StdExternalCrate"`, `imports_granularity = "Crate"`
  - `enum_discrim_align_threshold = 20`, `struct_field_align_threshold = 20`

## HashMap choice
Use `ahash::AHashMap` rather than `std::collections::HashMap`. The whole crate (including `SynonymMap`) is built on AHash; introducing std hashing would be inconsistent and slower for the workloads the crate sees.

## Docopt struct field naming (public API convention)
When a user derives `Deserialize` for their Args struct, field names map from usage-string tokens like this:
- `-g`          → `flag_g`
- `--group`     → `flag_group`
- `--group <arg>` → `flag_group`
- `FILE`        → `arg_FILE`
- `<file>`      → `arg_file`
- `build`       → `cmd_build`

Getting a prefix wrong is a **silent runtime field-miss**, not a compile error. Internal code that constructs or inspects these names must respect the same convention.

## Argument ingestion is lossy-UTF-8
The crate reads `std::env::args_os()` internally and does a **lossy** UTF-8 conversion — non-UTF-8 bytes become U+FFFD instead of panicking. Callers needing byte-exact argv must supply it via `.argv(...)`. Preserve this behavior when touching argv-ingestion code paths.

## Error / exit idiom
Both `.parse()` and `.deserialize()` return `Result<_, Error>`. The canonical usage in examples and tests is:
```rust
let args = Docopt::new(USAGE)
    .and_then(|d| d.deserialize())
    .unwrap_or_else(|e| e.exit());
```

## Naming
- Module and file names: `snake_case` (`dopt.rs`, `parse.rs`, `synonym.rs`, `utils.rs`, `wordlist.rs`).
- Types: `UpperCamelCase` (`Docopt`, `ArgvMap`, `SynonymMap`, `Pattern`, `Atom`).
- The crate intentionally keeps module names terse (`dopt`, not `docopt`) since they live under `qsv_docopt::`.

## Doc comments
Public items carry Rust doc comments (`///`) — sometimes with runnable examples that are compiled as doctests by `cargo test`. Keep doc examples working when refactoring signatures.

## Tests
- Hand-written integration-style tests live in `src/test/mod.rs` and `src/test/suggestions.rs`, driven by the `test_expect!` / `test_user_error!` macros defined at the top of `src/test/mod.rs`.
- The large `src/test/testcases.rs` is **generated** from `src/test/testcases.docopt` via `scripts/mk-testcases` — do not hand-edit; regenerate from the `.docopt` source and commit both.
