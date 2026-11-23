# 12. Security

A kernel is a security component. Its job is to reject false proofs, and its users include competitions, AI pipelines and bounty programmes in which the input author gains from a wrong accept. The 2026 incidents (research/A section 2) show that such authors exist and that they use models to find bugs. This document gives the threat model and the rules that follow from it.

## 12.1 Assets

| Asset | What a loss looks like |
|---|---|
| soundness of accept | rulean accepts a proof of a false statement |
| parity | rulean accepts what the official kernel rejects (used to get a proof past rulean that fails elsewhere), or the reverse |
| availability | a crafted input crashes rulean, hangs it, or exhausts memory, so that a judge cannot get a verdict |
| integrity of reports | the report names the wrong input, the wrong axioms or the wrong tool version |
| the host | a crafted input makes rulean read or write files or run code |

## 12.2 Attackers

| Attacker | Capability | Example |
|---|---|---|
| A1, proof author | writes any `.lean` file, including metaprograms that call `addDecl` with any term | the #14576 exploit used a raw `addDecl` (A§2.1) |
| A2, export author | writes any byte sequence as an NDJSON, `.rlb` or `.olean` file | a malformed olean that crashes the official importer (I#16542) |
| A3, model-assisted | A1 or A2 with large compute and models that read rulean's source | the 2026 bug hunt and the Opus 4.6 Rocq findings (A§2.4) |
| A4, supply chain | changes a dependency, a toolchain component or a proof file | |

rulean does not defend against an attacker who controls the machine that runs it.

## 12.3 Rules for hostile input

1. **Every input byte is hostile.** This includes `.olean` files, which the official loader trusts (07.3.3).
2. **No panics on input.** Every input error is a `Result` error. A panic on any input is a bug of the highest class. Fuzzing checks this (11.5).
3. **No recursion on input depth.** All traversals of terms use explicit stacks (05.11). A term of depth 10^8 gives a resource error or a verdict, never a stack overflow.
4. **Bounded memory.** Every allocation is checked against `--max-memory`. The current state is in 05.11.1: the store, the caches, the value arena, the session, the input buffers, the index tables of the NDJSON parser, the list of declarations and the buffers and tables of the olean reader are in the measure. An index above 2^28 is a decline, and an index table grows only after a budget check, so a single line cannot make the parser allocate a table above the budget.
5. **Bounded literals.** A Nat literal above 128 MiB is a reject before it is converted (05.8). Operations whose result would exceed the bound are refused before they run.
6. **No trust in cached data.** Hashes, flags, recursors, constructor counts and Quot types from the input are recomputed (06.1, 07.3.3).
7. **Hash flooding.** Table hashes are deterministic, so an attacker can make collisions. Collisions only cost time. Each table has a probe-length bound. Past the bound, the table switches that bucket to a sorted overflow list, which keeps lookups at O(log n). A run with many collisions is slower but still correct.
8. **Time.** `--timeout` bounds the wall time. Judges should always set it. At the deadline, the result is the resource code (05.11.1).

## 12.4 Rules for the code

- `#![forbid(unsafe_code)]` in every crate except `rulean-io` (the mapping call and the SHA instructions), `rulean-pool` (atomics) and `rulean-ffi` (the Lean ABI). Each `unsafe` block in those crates has a comment with the invariant and a Kani or Verus harness where possible.
- In `rulean-io`, only the module `sha` has `unsafe` code. It computes the SHA-256 digest of the input with the SHA extensions of x86_64 (SHA-NI) or the SHA2 extension of aarch64, and it finds the extension at run time. Without the extension, it uses the portable code of `rulean_core::sha256`. The `unsafe` blocks are the call of the functions with `#[target_feature]` and the loads and stores of the 128-bit registers. Kani does not model these instructions, so the tests compare the two codes on the test vectors of FIPS 180-4 and on each length from 0 to 1099 bytes. The CI test jobs run them on x86_64 and on aarch64. The digest is in the report and is not an input of the type checker, so a wrong digest cannot change a verdict. It can only make `confirm` (10.7, K2) see a change that did not happen, or not see a real one.
- `panic = "abort"` in all profiles, so a bug cannot leave a half-updated state that later code reads (K6, 10.7).
- `overflow-checks = true` in all profiles (K5).
- No network access, no process spawning (except `--paranoid` and `rulean diff`, which run named checkers), no file writes except the report.
- The CLI drops privileges it does not need. On Linux it can run under `seccomp` with a fixed system call list (`--sandbox`). On macOS it uses the App Sandbox profile in the release package. The sandbox is defence in depth, not part of the theorem.

## 12.5 Soundness defence in depth

| Layer | Defence |
|---|---|
| specification | con-leche's model, reviewed; extensions X1 to X8 each with a soundness proof (10.2) |
| algorithm | the twin's refinement proof (R1) |
| code | the Aeneas refinement proof (R2) |
| islands | contracts K1 to K6 with Verus, Kani and review (10.7) |
| compiler and platform | kernel diversity: `--paranoid` runs con-agua; users can also run `lake check --paranoid` (10.8) |
| primitives | primitive pinning (05.8) |
| testing | the whole of 11 |

The theorem does not cover the `.olean` reader and the in-process conversion. Users who need the theorem's guarantee should check NDJSON exports, as `lake check` does inside its sandbox (A§4.3).

## 12.6 Supply chain

- Dependencies of the verified core: none outside the rulean workspace, `core` and `alloc` (03.3).
- Dependencies of the whole workspace are listed and reviewed in `deny.toml`. The policy is in 13.3.
- `Cargo.lock` is committed. Releases are built with `--locked` in Nix with a pinned toolchain (13.3).
- Release binaries are reproducible. Two independent builders must get the same hash before a release is published.
- Proof files under protection (10.9) need two maintainer approvals.

## 12.7 Disclosure

- `SECURITY.md` from the first public commit. The 2026-08-02 advisory noted that Lean had no such file (A§2.1).
- Private reports go to a security address. The target is a fix or a public advisory within 14 days for a soundness bug.
- Each soundness bug gets a CVE request, a regression test, a postmortem in the repository and a row in a public `SOUNDNESS.md` history.
- A soundness bug in a released version is announced to the Lean Zulip and to the Arena maintainers on the day of the fix.
