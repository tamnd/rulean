# Contributing

Thank you for your help. This file gives the rules for code, proofs and text.

## Before you start

Read `docs/spec/00-README.md`. The spec settles the design. If a change does not agree with the spec, change the spec in the same pull request and say why.

## Build and test

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo xtask all
```

`cargo xtask all` checks the dependency rule and the no-C policy. It runs `cargo vendor`, so it needs the network on the first run.

The toolchain is pinned in `rust-toolchain.toml`. rustup installs it on the first build.

## Pull requests

- One topic for each pull request.
- Each pull request has one `area/*` label and one `type/*` label, and it refers to the issue of its milestone.
- A change that a user can see adds a line to `CHANGELOG.md` under "Unreleased".
- A change of behaviour needs a test.
- We merge with squash. The title of the pull request becomes the commit message, so write it as a short imperative sentence.

## Rules for the code

- No C, C++ or assembly in the tree or in the build of a dependency. See spec section 13.3.
- No `unsafe` outside the crates that the spec names (12.4).
- No panic on any input. An input fault is an error value (12.3).
- No recursion on the depth of an input term (05.11).

## Rules for text

All text in the repository (docs, comments, commit messages, issues, pull requests, release notes) follows ASD-STE100 Simplified Technical English as a guide. Use short sentences, the active voice and one idea in each sentence. Do not use em dashes. Put each paragraph on one line. See spec section 00.4.

## Licence

By contributing, you agree that your work is licensed under Apache-2.0 and MIT, as the repository is.
