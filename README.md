# rulean

rulean is a kernel for Lean 4, written in Rust. It reads the declarations of a Lean environment and checks each one, as the official Lean kernel does.

The project has three goals:

1. **Speed.** rulean must use at most one tenth of the CPU instructions of the official kernel of the same Lean release, on Mathlib, with the parser included.
2. **Parity.** rulean must give the same verdict as the official kernel on every environment that a Lean program can make.
3. **Soundness.** A proof in Lean must show that each environment that rulean accepts has a model in set theory. So rulean cannot accept a proof of `False`.

rulean contains no C or C++ code. It has its own big number type and uses no C allocator.

## Status

rulean is at an early stage. Engine R, the reference type checker, checks NDJSON exports and `.olean` files. The proofs of soundness and the fast engine are not done yet. The table shows the plan from `docs/spec/14-milestones.md`.

| Milestone | Content | State |
|---|---|---|
| M0 Foundations | repository, CI, the no-C checks, the Aeneas subset lint, the proof package, the bench harness | in progress |
| M1 Store and parser | the term store, the Nat type, the NDJSON parser | in progress |
| M2 Engine R | the reference type checker, inductive types, quotients | in progress |
| M3 Engine F | the fast type checker and the confirm set | in progress |
| M4 Scale | sessions, parallel checking, the binary format, the `.olean` reader | in progress |
| M5 Capstone | the soundness theorem with no `sorry` | planned |
| M6 In-process | rulean as the kernel inside Lean | planned |
| M7 Release 1.0 | the release gate, a security review, reproducible builds | planned |

## Install

Download a binary from the releases page, or build from source:

```sh
cargo build --release
target/release/rulean version
```

For a corpus with more than 2^27 expression nodes of one kind, build with `--features wide`. This build has 64-bit expression handles and uses more memory.

## Use

```sh
rulean check export.ndjson
rulean check --report report.json export.ndjson
rulean check --profile v4.35 export.ndjson
rulean pack export.ndjson -o export.rlb
rulean check export.rlb
rulean check --threads 4 export.ndjson
rulean check --format text --axioms std export.ndjson
rulean olean --path ~/.elan/toolchains/leanprover--lean4---v4.36.0/lib/lean Init
```

The input is an export in the NDJSON format of [lean4export](https://github.com/leanprover/lean4export), or `-` for standard input. `rulean pack` writes the binary format of `docs/spec/07-input-formats.md` (07.2). This format is a cache of the export with less parse work, and `rulean check` finds it from its first bytes. rulean selects the semantics profile from the Lean version of the export. Use `--profile` for an export from a Lean version that has no profile. The JSON report follows `docs/report.schema.json`. After the check, rulean reads the input file again. If the file changed during the run, the exit code is 4 and the report gives no verdict.

`--threads N` checks the declarations on N threads with the scheduler of spec 08.3. The verdict and the rejected declaration are the same as with one thread. Each thread has a copy of the term store, so the memory grows with N. The default is one thread.

`rulean olean MODULE...` reads the modules and their imports from `.olean` files, and checks them as `rulean check` does. It takes the options of `rulean check`. `--path DIR` adds a directory to the search path, and without `--path` the search path comes from `LEAN_PATH`, so `lake env rulean olean MODULE` uses the search path of a project. The reader treats each byte of a file as hostile input. It reads olean format version 2 with the GMP number encoding, which Lean v4.33 to v4.36 write, and declines other versions. For a module of the module system, it reads the `.olean.private` file too, so that it checks the proofs.

`--axioms LIST` gives the axioms that a theorem can use. LIST is `any` (the default), `none`, or names with a comma between them. The name `std` means `propext`, `Quot.sound` and `Classical.choice`. If every declaration is accepted but a theorem uses an axiom outside the list, the exit code is 5. The axioms of a theorem are the axioms that `#print axioms` shows. The last command above is the command for an external kernel of `lake comparator`. Lake adds the path of the export at the end, so the entry in `comparator.json` is:

```json
"external_kernels": {"rulean": ["rulean", "check", "--format", "text", "--axioms", "std"]}
```

In Lean v4.35.0 and v4.36.0, `lake check` runs only the kernels that come with Lean, so it does not run rulean.

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
