# Suggested Commands

## Build
```bash
cargo build              # debug
cargo build --release
```

## Test
```bash
cargo test               # full suite (library tests + generated testcases.rs)
cargo test <substring>   # run a single test whose name contains <substring>
cargo test --verbose     # what CI runs
```

## Format
The project's `rustfmt.toml` uses **nightly-only** options (`wrap_comments`, `format_strings`, `group_imports`, `imports_granularity`, `*_align_threshold`). Stable `cargo fmt` silently skips them.
```bash
cargo +nightly fmt
```

## Regenerate test fixtures
`src/test/testcases.rs` is a **checked-in generated file** produced from `src/test/testcases.docopt`. CI does not regenerate it, so a stale `.rs` quietly tests against old fixtures.
```bash
./scripts/mk-testcases ./src/test/testcases.docopt > ./src/test/testcases.rs
# equivalent:
make src/test/testcases.rs
```

## Lint
No Clippy configuration is checked in and CI does not run it, but ad-hoc checks are fine:
```bash
cargo clippy --all-targets
```

## Docs
```bash
cargo doc --open
```

## Examples (under `examples/`)
```bash
cargo run --example cp -- -a file1 file2 dest/
cargo run --example cargo
cargo run --example decode
cargo run --example hashmap
cargo run --example optional_command
cargo run --example options_from_usage
cargo run --example verbose_multiple
```

## Binary
```bash
cargo run --bin docopt-wordlist -- <args>
```

## System utilities (Darwin / macOS)
Standard BSD variants of `ls`, `find`, `grep`, `sed`, `awk` are available — note they lack many GNU-only flags. `git` works as usual. Prefer ripgrep (`rg`) if installed.
