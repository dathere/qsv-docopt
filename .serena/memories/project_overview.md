# qsv_docopt — Project Overview

## What it is
A Rust crate that implements [Docopt](http://docopt.org/) — a command-line argument parser derived from the program's self-documenting usage string. Supports automatic type-based decoding via serde (data validation happens as part of parsing).

## Why this fork exists
`qsv_docopt` is a maintained fork of the upstream [docopt.rs](https://github.com/docopt/docopt.rs), which is no longer maintained. It is kept alive specifically for the [qsv](https://github.com/jqnatividad/qsv) CSV toolkit, whose self-documenting usage-string approach cannot be replicated with `clap` or `structopt`.

## Artifacts produced
- Library crate `qsv_docopt` (the main product).
- Binary `docopt-wordlist` (`src/wordlist.rs`) — a bash tab-completion helper; not documented by default (`doc = false`, `test = false` in `Cargo.toml`).

## Two parallel result APIs
- `Docopt::new(USAGE).and_then(|d| d.parse())` → untyped `ArgvMap` with `get_bool` / `get_count` / `get_str` / `get_vec` accessors.
- `Docopt::new(USAGE).and_then(|d| d.deserialize())` → strongly-typed user struct via serde `#[derive(Deserialize)]`.

## Licensing
Dual-licensed MIT / UNLICENSE (see `LICENSE-MIT`, `UNLICENSE`, `COPYING`).

## Repo URL
`https://github.com/dathere/qsv-docopt`
