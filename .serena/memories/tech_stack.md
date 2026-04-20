# Tech Stack

## Language / edition
- Rust, edition **2024**.
- MSRV **1.95** (per `Cargo.toml` `rust-version`).

## Runtime dependencies (`Cargo.toml`)
- `regex` 1 — pattern matching inside the parser.
- `serde` 1 with `derive` — powers typed `.deserialize()`.
- `strsim` 0.11 — "did-you-mean" suggestions for unknown flags.
- `ahash` 0.8 — the crate uses `ahash::AHashMap` in place of `std::collections::HashMap` throughout. Follow suit when adding new maps.

## Build system
- Plain Cargo. A `Makefile` exists but only wraps a couple of legacy targets (docs publish, ctags, push); day-to-day work uses `cargo` directly.
- `scripts/mk-testcases` is a shell script used to regenerate `src/test/testcases.rs` from `src/test/testcases.docopt`.

## CI
- `.github/workflows/{linux,macos,windows}.yml` — each runs only `cargo build --verbose` and `cargo test --verbose`. There is **no** lint or format gate in CI.
