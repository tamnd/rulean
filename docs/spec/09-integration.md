# 09. Integration

This document specifies how people and tools use rulean: the command line, the reports, the integration with `lake check` and `lake comparator`, and the in-process kernel that replaces the C++ kernel inside a Lean process.

Sources: research/A section 4 (leanchecker, lake check, comparator), research/D section 4 (in-process options and the ABI).

## 09.1 Modes

| Mode | Input | Output | Milestone |
|---|---|---|---|
| external checker | NDJSON or `.rlb` file, or standard input | verdict, report, exit code | M2 |
| olean checker | a module name and a search path | as above | M4 |
| Arena checker | `$IN` from the Arena | exit 0, 1 or 2 | M2 |
| `lake check` kernel | the NDJSON export inside the sandbox | exit code and report | M3 |
| in-process kernel | Lean `Declaration` objects through `lean_add_decl` | a Lean `Except Kernel.Exception Environment` | M6 |

## 09.2 Command line

```
rulean check   [OPTIONS] <INPUT>          check an export (.ndjson, .ndjson.zst, .rlb) or "-" for stdin
rulean olean   [OPTIONS] <MODULE>...      check modules from .olean files (07.3)
rulean pack    <INPUT> -o <OUT.rlb>       write the binary format (07.2)
rulean diff    <INPUT> --against <CMD>    run another checker and compare verdicts per declaration (11.3)
rulean explain <INPUT> <DECL>             check one declaration with a full trace of rule applications
rulean version                            print versions, commits, profile list and the proof commit
```

Main options:

| Option | Default | Meaning |
|---|---|---|
| `--profile <id>` | from the input | semantics profile (05.2) |
| `--path <dir>` | `LEAN_PATH` | `rulean olean` only: a directory of the search path. More than one is allowed, and the first directory that has the module wins. Without `--path`, the directories of `LEAN_PATH` are the search path. |
| `--threads <n>` | 1 | worker count (08.3); 1 is the sequential check, and the plan is the number of cores (08.3.5) |
| `--report <file>` | none | write the JSON report (09.4) |
| `--format text\|json` | text | the format of standard output |
| `--axioms <list>` | any | reject if a theorem uses an axiom outside the list; `std` means {propext, Quot.sound, Classical.choice} |
| `--limits official\|default` | default | 05.11 |
| `--max-memory`, `--timeout` | 05.11 | resource limits |
| `--engine F\|R` | F | engine R only, for debugging (05.5) |
| `--confirm default\|all` | default | the confirm set (05.1) |
| `--session on\|off` | on | keep the session caches across declarations (08.4); `off` clears all caches at each declaration, as the official kernel does |
| `--rules official\|con-leche` | official | 05.12, D4 |
| `--trust-primitives-by-name` | off | 05.12, D1 |
| `--no-simd` | off | island K4 off (10.7) |
| `--paranoid` | off | after the check, also run con-agua (if installed) on the same input and require it to accept (10.8) |

## 09.3 Exit codes

The Arena uses 0 (accept), 1 (reject) and 2 (decline). rulean keeps those codes and adds more specific ones above 2, which every Arena-style caller reads as "not accepted":

| Code | Meaning |
|---|---|
| 0 | accept: every declaration was accepted |
| 1 | reject: at least one declaration was rejected |
| 2 | decline: rulean does not support this input (unknown format version, unknown Lean version, a feature outside the profile) |
| 3 | resource: a limit was reached and no declaration was rejected |
| 4 | input error: the file is malformed (bad JSON, bad olean structure) |
| 5 | axiom policy: every declaration was accepted, but a theorem uses an axiom outside `--axioms` |
| 64 | usage error |

For the Arena entry, codes 3 to 5 map to 1 or 2 in the wrapper script, as the Arena rules require. An input error maps to 1, because a malformed export is a reject in the Arena's sense.

## 09.4 Reports

The JSON report follows the structure of 03.4.2. It is stable: fields are only added, and the schema has a version. The schema is in `docs/report.schema.json`.

Example (shortened):

```json
{
  "schema": "rulean-report/1",
  "tool": { "rulean": "1.0.0", "commit": "…", "proof_commit": "…", "build": "verified" },
  "input": { "format": "ndjson-3.1.0", "sha256": "…", "lean_version": "4.36.0", "profile": "v4.35" },
  "verdict": "accept",
  "summary": {
    "declarations": 701234, "accepted": 701234, "rejected": 0, "quarantine": 0,
    "axioms_used": ["Classical.choice", "Quot.sound", "propext"],
    "deviations": [], "wall_ms": 41210, "peak_rss_bytes": 3758096384
  },
  "decls": "omitted unless --report-decls"
}
```

Rules:

- The per-declaration list is written only with `--report-decls`, because it is large for Mathlib. With `--report-axioms`, the list has only theorems and their axioms (P2.c).
- Axiom lists are computed as the official `#print axioms` does: the axioms in the transitive closure of the constants that the declaration uses, through types and values (T4, 10.1). Natively evaluated facts appear as `_native.…` axioms.
- The input hash is SHA-256 over the exact bytes that were checked (contract K2, 10.7). SHA-256 is implemented in pure Rust (13.3).
- Specs 2148 and 2148r replay trust reports with a second kernel. They read this report format.
- The field `slowest` lists the 10 slowest declarations of a sequential run, with the wall time of each in microseconds. It shows where the time of a run goes, for the performance work of 08.7. The list is empty with `--threads` above 1.

## 09.5 `lake check`, `lake comparator` and the Arena

- **`lake check`.** Lean v4.35.0 added `lake check` and `lake comparator` with external kernels (A§4.3). Both commands export the project in a `bwrap` sandbox and run kernels on the export. `lake comparator` runs the kernels of the `external_kernels` field of `comparator.json` first, then the bundled ones with `--paranoid`, then the built-in kernel. In v4.35.0 and v4.36.0, `lake check` runs only the bundled kernels and the built-in kernel, and it has no field for an external kernel. Lake adds the path of the export file at the end of the command of each kernel. So rulean is configured as an external kernel with the command `["rulean", "check", "--format", "text", "--axioms", "std"]`. rulean reads the NDJSON export from the sandbox and does not need network access or other files. The project in `tests/lake` and `scripts/lake-comparator.sh` test this interface with the real `lake comparator`.
- **Bundling.** The goal is to be bundled with Lean like con-ron (A§4.3, `CMakeLists.txt` pins). That is an upstream decision (15.4). rulean prepares for it: a reproducible build with Cargo only, no C dependencies, and a pinned commit.
- **`lake comparator`.** The comparator checks that the challenge and the solution agree on the theorem statements, the permitted axioms and the `primitiveTargets` (A§4.3). It uses a kernel for the check itself. rulean works there through the same external-kernel interface. rulean's primitive pinning (05.8) does the same job as the comparator's `primitiveTargets` check, from inside the kernel.
- **Arena.** rulean is submitted to the Lean Kernel Arena from M2, with its source commit and build script. Each release is re-submitted. The Arena results are the public evidence for P1 and P2.

## 09.6 In-process kernel

### 09.6.1 Goal

From milestone M6, a Lean process can use rulean as its kernel. Then every Lean program (the elaborator, tactics, `lake build`, `#eval` of meta code) runs with rulean deciding every `addDecl`. This is P2.d.

### 09.6.2 Mechanism

The four options are in D§4.1. rulean chooses:

1. **First, a build of Lean with rulean linked in.** rulean builds as a Rust `staticlib` that exports these symbols, with the official signatures:

   | Symbol | Lean side |
   |---|---|
   | `lean_add_decl(env, max_heartbeat, max_rec_depth, decl, cancel_tk)` | `Lean.Kernel.Environment.addDeclCore` |
   | `lean_add_decl_without_checking(env, decl)` | trusted bypass (D6, 05.12) |
   | `lean_kernel_is_def_eq(env, lctx, a, b)` | `Lean.Kernel.isDefEq` |
   | `lean_kernel_whnf(env, lctx, e)` | `Lean.Kernel.whnf` |
   | `lean_kernel_check(env, lctx, e)` | `Lean.Kernel.check` |

   The Lean build replaces `src/kernel` with these symbols. The C++ files in `src/library` that include kernel headers still need declarations. A thin header-only shim provides them. That shim is part of Lean's build, not of rulean (02.5, no-C rule applies to rulean's tree).
2. **Then, an upstream hook.** rulean proposes a Lean option that selects the kernel implementation at run time (D§4.1 option D). This needs upstream agreement (15.4).

Symbol interposition (option C) is not supported. It is fragile, and macOS blocks it for signed binaries.

### 09.6.3 The Lean object ABI in Rust

`rulean-ffi` talks to Lean objects in pure Rust:

- `#[repr(C)]` mirrors of `lean_object` and the constructor layouts of `Name`, `Level`, `Expr`, `Declaration` and `ConstantInfo` (D§2, D§3). The `static inline` functions of `lean.h` (`lean_inc_ref`, `lean_alloc_ctor`, …) are written again in Rust, as the `lean-sys` crate does.
- Ownership: `env` is owned, and `decl` and `cancel_tk` are borrowed (D§4.2). Reference counts follow the sticky-count rules of #14838.
- **Conversion at the boundary.** Lean objects are converted into the rulean store on entry. The checker never holds Lean objects. Results are converted back on exit. This keeps the verified core free of the Lean ABI.
- **Environment.** rulean keeps its own mirror of the kernel environment, keyed by the Lean environment's identity and the number of constants. A new `addDecl` on the same environment extends the mirror. An environment that rulean has not seen (for example after `import`) is mirrored from its constant map on first use, and the mirror is cached per imported module.
- **Cost of conversion.** The conversion is linear in the new declaration. For imports, it is linear in the imported constants, once per process. The target is at most 10% of the official kernel's time for the same declaration.

### 09.6.4 Heartbeats, cancellation and errors

- The cancel token is polled every 2^16 work units. A set token gives `Kernel.Exception.interrupted`.
- **Heartbeats.** The official kernel counts heartbeats as small allocations in the Lean runtime. rulean does not allocate the same way, so it cannot count the same number. rulean counts work units and maps them to heartbeats with a factor calibrated on Mathlib so that rulean's count is never above the official count for the same declaration. So rulean never times out where the official kernel does not. rulean may succeed where the official kernel times out. That is deviation D2 (05.12).
- **Errors.** Kernel errors are converted to the official `Kernel.Exception` constructors with the same fields (A§1.13). The local context and the terms in an error are converted back to Lean objects, so that the elaborator can print them.

### 09.6.5 Trust in in-process mode

In-process mode is not covered by theorem T1 (10.1). The input comes from Lean objects, not from bytes. The conversion layer is in the hardened class (03.2). It is tested by running the whole Lean test suite and a full `lake build` of Mathlib with the rulean kernel, and by comparing every `addDecl` result with the C++ kernel in a dual-kernel build (11.3).
