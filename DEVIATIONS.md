# Deviations

This file lists each known difference between rulean and the official Lean kernel of a profile. It is the deviation register of spec 05.12. `docs/deviations.json` has the same rows in a form that a program can read. A release cannot add a deviation without a row here and in that file, and the changelog lists each change of a row.

A deviation is a difference in the verdict or in the report on one class of input. On each input outside these classes, rulean must give the verdict of the official kernel of the profile (promise P2). A difference outside these classes is a parity bug. Report it as an issue with the label `parity`.

The JSON report has the field `summary.deviations` for the rows that apply to the input. Now only D1 sets this field.

## The register

| ID | Input class | Official kernel | rulean default | Option | State | Tests |
|---|---|---|---|---|---|---|
| D1 | an export that redefines a primitive (`Nat.add`, `String.ofList` and the other pinned names) with another value | uses the built-in operation | unfolds the definition of the export (spec 05.8) | `--trust-primitives-by-name` gives the official behaviour, outside T1 | in place | `crates/rulean-core/tests/pin.rs` |
| D2 | a declaration where the official kernel hits a resource limit and rulean does not | resource error | accept, with a flag | `--limits=official` | planned | none |
| D3 | the Arena tests with the outcome "either" | depends on the profile | the verdict of the official kernel of the profile | none | in place for v4.35 and v4.37 | `docs/arena/either-v4.35.tsv`, `docs/arena/either-v4.37.tsv`, the CI job `arena-either` |
| D4 | rules that con-leche has and the official kernel does not: semantic level comparison, proof irrelevance fall-through, the `And.rec` rescue and extra large elimination | reject | reject | `--rules=con-leche` accepts, and T1 still covers it | planned | none |
| D5 | `.olean` input whose cached hashes or flags do not agree with the values that rulean computes | uses the cached data with no check | ignores the cached data and computes the values again; gives the input error (exit code 4) if the structure is not valid (spec 07.3) | none | in place | the unit tests of `crates/rulean-olean`, the CI job `olean-xval` |
| D6 | a declaration with a trust level above 1024 in in-process mode | adds the declaration with no check | adds the declaration with no check and marks the constant `unchecked` in the report | `--check-all` checks it | planned | none |

Rows D1 and D5 can differ from the official kernel only on inputs that no Lean program makes without metaprogramming.

## Notes on each row

**D1.** Spec 05.8 pins each primitive by name and by the hash of its definition. If an export has a primitive with the pinned name and a different definition, the extension is off for that name, and the constant unfolds as each other definition does. The report lists the names in `pin_mismatch`, and `summary.deviations` has `D1`. The official kernel uses the built-in operation and does not look at the definition.

**D2.** rulean does not have the option `--limits=official` yet. Two Arena tests in the "either" group have no verdict of the official kernel v4.35.0, because the official kernel ran out of time on them: `corner-cases/eta-struct-major-and-no-whnf` and `corner-cases/eta-struct-major-no-whnf`. The CI job `arena-either` does not run them with the profile v4.35. The official kernel of v4.37.0-rc1 accepts both tests, so the profile v4.37 has a verdict for them.

**D3.** The Arena has no fixed answer for its 30 "either" tests, and the official verdicts of v4.35.0 and of the nightly of 2026-11-14 are different on 8 of them (spec 11.3). rulean pins the answer of each profile to the official verdict. For v4.35, `docs/arena/either-v4.35.tsv` has the verdict of the official kernel v4.35.0 in the Arena results of 2026-11-21. The CI job `arena-either` builds the 30 tests and requires that rulean gives the verdict of that file on the 28 tests that have one. So on these tests, rulean gives the same verdict as the official kernel. For v4.37, `docs/arena/either-v4.37.tsv` has the verdict of `leanchecker --from-export` of v4.37.0-rc1 on the same exports. The job runs that leanchecker with `scripts/arena-official.sh` and requires the verdicts of the file, then requires the same verdicts from rulean with `--profile v4.37` on the 30 tests. The four `eta-unit-like-*` tests differ from the nightly of 2026-11-14, because lean4#15372 was reverted before v4.37.0-rc1.

**D4.** The options of D4 are not in rulean yet. By default rulean rejects these inputs, as the official kernel does.

**D5.** The `.olean` reader (`rulean olean`) ignores the cached data of each term, level and name: the hash, the flags, the range of loose bound variables and the depth. It makes the store nodes again, so these values come from rulean. The one exception is the cached name hash of the keys of the constant trie of format version 4, which the reader compares with its own hash (spec 07.3). If the structure of a file is not valid, `rulean olean` gives the input error, exit code 4. An earlier version of the register named a decline with the code `malformed-olean`. The input error is the code of each other malformed input (spec 09.3), so the register now uses it.

**D6.** In-process mode is milestone M6 and is not in rulean yet.
