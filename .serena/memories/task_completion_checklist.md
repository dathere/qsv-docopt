# Task Completion Checklist

Run these before declaring a change done. CI only runs build + test, so everything else is on the contributor.

## 1. If you edited `src/test/testcases.docopt`
Regenerate the companion file and commit both together:
```bash
./scripts/mk-testcases ./src/test/testcases.docopt > ./src/test/testcases.rs
```
Never hand-edit `src/test/testcases.rs` — it will be overwritten on the next regen and CI won't catch the drift.

## 2. Build
```bash
cargo build
```

## 3. Test
```bash
cargo test
```
Covers library tests, the generated testcases, doctests in public items, and the hand-written tests in `src/test/`.

## 4. Format (nightly only)
```bash
cargo +nightly fmt
```
If nightly isn't installed, state that explicitly rather than running stable `cargo fmt` — stable silently drops most of this project's style rules.

## 5. (Optional) Clippy
Not gated, but useful for non-trivial changes:
```bash
cargo clippy --all-targets
```

## 6. Sanity-check doc examples
The crate's doc comments contain executable examples that `cargo test` runs as doctests. If you changed a public signature in `src/dopt.rs` or `src/lib.rs`, verify the updated doctests pass.

## 7. MSRV guard
Project targets Rust **1.95** / edition 2024. Don't use unstable features or APIs newer than 1.95 without bumping `rust-version` in `Cargo.toml` deliberately.
