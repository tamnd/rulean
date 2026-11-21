# rulean

rulean is a kernel for Lean 4, written in Rust. It reads the declarations of a Lean environment and checks each one, as the official Lean kernel does.

The project has three goals:

1. **Speed.** rulean must use at most one tenth of the CPU instructions of the official kernel of the same Lean release, on Mathlib, with the parser included.
2. **Parity.** rulean must give the same verdict as the official kernel on every environment that a Lean program can make.
3. **Soundness.** A proof in Lean must show that each environment that rulean accepts has a model in set theory. So rulean cannot accept a proof of `False`.

rulean contains no C or C++ code. It has its own big number type and uses no C allocator.

## Status

rulean is at an early stage. It does not check proofs yet. The table shows the plan from `docs/spec/14-milestones.md`.

| Milestone | Content | State |
|---|---|---|
| M0 Foundations | repository, CI, the no-C checks, the Aeneas subset lint, the proof package, the bench harness | in progress |
| M1 Store and parser | the term store, the Nat type, the NDJSON parser | planned |
| M2 Engine R | the reference type checker, inductive types, quotients | planned |
| M3 Engine F | the fast type checker and the confirm set | planned |
| M4 Scale | sessions, parallel checking, the binary format, the `.olean` reader | planned |
| M5 Capstone | the soundness theorem with no `sorry` | planned |
| M6 In-process | rulean as the kernel inside Lean | planned |
| M7 Release 1.0 | the release gate, a security review, reproducible builds | planned |

## Install

Download a binary from the releases page, or build from source:

```sh
cargo build --release
target/release/rulean version
```

## Use

```sh
rulean check export.ndjson
```

The input is an export in the NDJSON format of [lean4export](https://github.com/leanprover/lean4export). The `check` command arrives in milestone M2. Until then it exits with code 2.

| Exit code | Meaning |
|---|---|
| 0 | accept |
| 1 | reject |
| 2 | decline: rulean does not support the input |
| 3 | a resource limit was reached |
| 4 | the input is malformed |
| 5 | an axiom is outside the allowed list |
| 64 | usage error |

Codes 0, 1 and 2 are the codes of the [Lean Kernel Arena](https://arena.lean-lang.org/).

## Documents

- [Specification](docs/spec/00-README.md): the design, the research of 2026, the proof plan and the milestones.
- [Changelog](CHANGELOG.md)
- [Security policy](SECURITY.md): how to report a soundness bug.
- [Contributing](CONTRIBUTING.md)

## Related work

rulean builds on the work of others. [con-leche](https://github.com/leanprover/con-leche) gives the model in set theory that the soundness theorem uses. [con-ron](https://github.com/leanprover/con-ron) showed that a Rust kernel can be proved correct through [Aeneas](https://github.com/AeneasVerif/aeneas). [nanoda](https://github.com/ammkrn/nanoda_lib), [nano-lean](https://github.com/sdiehl/nano-lean) and [gruszka](https://github.com/jasisz/gruszka) showed how fast a Lean kernel in Rust can be.

## Licence

rulean is licensed under either of [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your choice.
