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
| `--max-memory <size>\|none`, `--timeout <time>` | 05.11 | resource limits: a size such as `8G`, and a time such as `90s` or `2h` (05.11.1) |
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
- The fields `steps` and `interns` of `summary` are the work count of the run: the calls of `enter` of the type checker and the calls of `intern_expr` of the store, with the parse. A sequential run gives the same counts on each machine. The work gate of 08.7.4 uses them. With `--threads` above 1, the counts are the sums over the workers, and they can change from one run to the next.
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
   | `lean_elab_add_decl(env, max_heartbeat, max_rec_depth, decl, cancel_tk)` | `Lean.Environment.addDeclCore`, the elaborator |
   | `lean_elab_add_decl_without_checking(env, decl)` | `Lean.Environment.addDeclCore` without the check |
   | `lean_kernel_is_def_eq(env, lctx, a, b)` | `Lean.Kernel.isDefEq` |
   | `lean_kernel_whnf(env, lctx, e)` | `Lean.Kernel.whnf` |
   | `lean_kernel_check(env, lctx, e)` | `Lean.Kernel.check` |

   The elaborator of Lean v4.36.0 does not call `lean_add_decl`. `Lean.Environment.addDeclCore` calls `lean_elab_add_decl`, which is C++ code in `src/library/elab_environment.cpp`. That function makes the kernel environment of the `Lean.Environment`, adds the declaration with the C++ kernel, and gives the new kernel environment to `lean_elab_environment_update_base_after_kernel_add`. rulean exports `lean_elab_add_decl` and `lean_elab_add_decl_without_checking`, which do the same steps with rulean as the kernel. Thus a build that replaces only `lean_add_decl` still checks the declarations of the elaborator with the C++ kernel.

   The script `scripts/lean-build.sh` makes the build. It does not compile the C++ kernel again. The release of Lean v4.36.0 has the static libraries of Lean (`libLean.a`, `libStd.a`, `libInit.a`, `libleanrt.a`), and the C++ kernel and `src/library` are in `libleancpp.a`. The script makes a copy of `libleancpp.a` in which each symbol of the table has the suffix `_cpp`, with `llvm-objcopy --redefine-sym`. Then it links the libraries of the release, this copy and the static library of `rulean-ffi` into a new `lean` binary. The release has `lean_main` only in `libleanshared`, so the script compiles `src/util/shell.cpp` and `src/shell/lean.cpp` from the Lean source at the commit of the release. These two files are part of the Lean build, not of rulean (02.5, the no-C rule applies to the tree of rulean). Before the link, the script makes sure that the copy defines each `_cpp` symbol and not the old name, that `rulean-ffi` defines the old name, and that no object of Lean refers to a `_cpp` symbol. Thus each call of Lean to a symbol of the table goes to rulean. The C++ functions stay in the binary with the new names, so the dual-kernel build can call them. The new binary uses the `lib` and `include` directories of the release.

   At this time the script works on macOS only. The test file `tests/lean-build/smoke.lean` has inductive types with `deriving`, structural, mutual and well-founded recursion, `simp`, `omega`, `decide`, `#eval`, a declaration that the kernel rejects, and calls of `Kernel.whnf` and `Kernel.isDefEq`. The CI job `lean-build` runs it with the `lean` of the release and with the new `lean` on macOS, and the two outputs must be the same. `declHasMVars` is a known difference: the conversion declines a term with a metavariable, so rulean gives `other` with the reason of the conversion (09.6.4).

   The feature `export` of `rulean-ffi` gives these symbols. The command `cargo rustc -p rulean-ffi --release --features export --crate-type staticlib` makes the static library. Each thread that calls a symbol gets its own `Kernel` (09.6.3), and the `Kernel` finds the functions of the Lean runtime in the images of the process. The library exports `lean_add_decl`, `lean_add_decl_without_checking`, `lean_elab_add_decl` and `lean_elab_add_decl_without_checking`. For an axiom, a definition, a theorem, an opaque constant and a mutual block, rulean adds the `*Val` object of the declaration as the C++ kernel does, so the terms keep their `mdata`. `lean_add_decl_without_checking` does what the C++ kernel does when `check` is false: these kinds get no check, except that a mutual block must not be empty and must be unsafe or partial. An inductive block and the quotient get the full check.

   The library also exports `lean_kernel_is_def_eq`, `lean_kernel_whnf` and `lean_kernel_check`. Each call consumes its arguments. The `env` argument is a `Lean.Environment`, and the call takes its kernel environment with `lean_elab_environment_to_kernel_env`, as the C++ functions do. rulean reads the field `decls` of the `LocalContext` and gives each local declaration a free variable of the checker, in the order of the declarations. A `let` declaration has its value, so `whnf` replaces a `let` free variable with its value, as the C++ kernel does. The checker is safe and has no universe level parameters, and `check` does not look at the level parameters of the term, as `type_checker::check` without parameters does. The mirror has the constants that the types and the values of the local context and the terms refer to, and their closure (09.6.3). These functions have two known differences from the C++ functions. A free variable that is not in the local context is an error in rulean, but the C++ `whnf` and `is_def_eq` can give a result for it. The result of `whnf` and `check` has no `mdata`, because the conversion into the store removes `mdata`.
2. **Then, an upstream hook.** rulean proposes a Lean option that selects the kernel implementation at run time (D§4.1 option D). This needs upstream agreement (15.4).

Symbol interposition (option C) is not supported. It is fragile, and macOS blocks it for signed binaries.

### 09.6.3 The Lean object ABI in Rust

`rulean-ffi` talks to Lean objects in pure Rust:

- `#[repr(C)]` mirrors of `lean_object` and the constructor layouts of `Name`, `Level`, `Expr`, `Declaration` and `ConstantInfo` (D§2, D§3). The `static inline` functions of `lean.h` (`lean_inc_ref`, `lean_alloc_ctor`, …) are written again in Rust, as the `lean-sys` crate does.
- Ownership: `env` is owned, and `decl` and `cancel_tk` are borrowed (D§4.2). Reference counts follow the sticky-count rules of #14838.
- **Conversion at the boundary.** Lean objects are converted into the rulean store on entry. The checker never holds Lean objects. Results are converted back on exit. This keeps the verified core free of the Lean ABI.
- **Environment.** rulean keeps a mirror of the kernel environment for each thread: a checker and, for each constant of its environment, the `ConstantInfo` object that the constant came from. The mirror keeps a reference to each of these objects, so the Lean runtime cannot free an object or change it in place. Thus an object at the same address is the same constant. A Lean environment is a persistent value, and two environments can have different constants with the same name, so the identity of the environment object is not a key. Each `addDecl` walks the constants that the check can use: the constants of the declaration, the constants of their types and values, the families of the inductive types, and the constants that the checker knows by name. It finds each one with `lean_environment_find`. A constant with the same object is not converted again. If the walk finds a constant of the mirror that the Lean environment does not have or has with a different object, or if only the mirror has the quotient, rulean makes a new mirror. A constant of the mirror that the walk does not find has no effect on the check. After an accepted declaration, the mirror records the objects of the new constants in the result environment, so the next `addDecl` on that environment converts no constant again. After a rejection, the mirror removes the new constants. The checker of the mirror has no session (08.4), so the heartbeats of a declaration do not depend on the earlier calls. A mirror above 2 GiB is dropped at the next call, because the store keeps the terms of each declaration. A cancelled check drops the mirror. The term functions use a new mirror for each call. The test `dual` checks the declarations of the test on the result environments of rulean, and the mirror converts no constant of the Lean environment. Then two environments get a constant `c` with different values, and a definition that uses `c` gets the verdict of the C++ kernel on each environment.
- **Cost of conversion.** The conversion is linear in the new declaration. For imports, it is linear in the imported constants, once per process. The target is at most 10% of the official kernel's time for the same declaration.

### 09.6.4 Heartbeats, cancellation and errors

- **Cancellation.** The C++ kernel of Lean v4.36.0 reads the cancel token at each heartbeat, in `check_system`, and a set token gives `Kernel.Exception.interrupted`. It reads only the flag `setRef`, which is field 1 of `IO.CancelToken`. rulean reads the same flag. If `lean_add_decl` gets a token, rulean converts the declaration and mirrors the constants on the calling thread, and then checks the declaration on a new thread with a stack of 1 GiB. The calling thread reads the token each millisecond until the check stops. If the token is set, the call gives `interrupted` at once. The check continues on its thread until it stops, and rulean discards its result. The check uses no Lean object, so this is safe. The core checker has no point at which it can stop, so a cancelled check uses a processor until it ends. A token that is set before the call gives `interrupted` before the check starts. The C++ kernel gives `interrupted` only at its first heartbeat, so a declaration that it checks without a heartbeat, such as the quotient, is accepted. The test `dual` gives each accepted test declaration to the two kernels with a set token and with a token that is not set. The C++ kernel gives `interrupted` for 7 of the 8 declarations and accepts the quotient, and rulean gives `interrupted` for all 8. Without a token, the check runs on the calling thread. The term functions get no token.
- **Heartbeats.** The elaborator counts heartbeats as small allocations in the Lean runtime, but the kernel of Lean v4.36.0 has a different counter. `check_system` adds one kernel heartbeat at the start of each call of `infer_type_core`, `whnf_core` and `is_def_eq_core`, and the kernel gives `deterministicTimeout` when the count is above `max_heartbeat`. The counter is for each thread, and the task manager sets it to 0 at the start of each task, not of each declaration. A limit of 0 is no limit. rulean counts one heartbeat at the same three functions of engine R and starts at 0 for each declaration. Engine F and the fast paths of rulean before these calls count no heartbeats. The rule is that rulean's count is never above the official count for the same declaration, so rulean never times out where the official kernel does not. rulean may succeed where the official kernel times out. That is deviation D2 (05.12). The factor from the count of rulean to heartbeats is 1 at this time. The test `dual` finds the smallest limit with which each kernel accepts each test declaration, and requires that the count of rulean is not above the count of the C++ kernel. For the 8 accepted declarations of the test, rulean counts between 69% and 100% of the C++ count. A calibration on Mathlib needs the dual-kernel build (11.3). The term functions `lean_kernel_is_def_eq`, `lean_kernel_whnf` and `lean_kernel_check` have no limit in rulean, because the C++ functions use the limit of the thread and Lean does not export it.
- **Errors.** A rejection gives the `Kernel.Exception` constructor of the C++ kernel with the same fields (A§1.13). rulean maps the kinds `unknownConstant`, `alreadyDeclared`, `declTypeMismatch`, `funExpected`, `typeExpected`, `letTypeMismatch`, `appTypeMismatch`, `invalidProj`, `thmTypeIsNotProp`, `deterministicTimeout`, `excessiveMemory`, `deepRecursion` and `interrupted`. The kinds `declHasMVars`, `declHasFVars` and `exprTypeMismatch` are not mapped yet, and they give `other` with a message. The errors that the C++ kernel gives as `other` also give `other`. The terms of an exception go back to Lean as `Expr` objects, so that the elaborator can print them. The check of a declaration makes its terms in the scratch tier of the store (04.8), and the check clears this tier at its end. Thus, after a rejection in in-process mode, the checker first copies the terms of the fault and the types and the values of the local context into the frozen tier. The local context of an exception is a `LocalContext` object, which rulean makes with `lean_mk_empty_local_ctx`, `lean_local_ctx_mk_local_decl` and `lean_local_ctx_mk_let_decl`. A free variable of the local context of a term function keeps its `FVarId`. A free variable that the check makes gets the name `_kernel_fresh.N`. The C++ kernel removes the free variables of a binder at the end of its scope, but the checker of rulean keeps each free variable of the check. Thus the local context of rulean can have more declarations than the context of the C++ kernel, and it has each free variable of the terms of the exception. If a term of an exception cannot be converted, the exception is `other` with the reason. The test `dual` gives 10 declarations and 5 terms that the two kernels reject. For each one, the two kernels give the same constructor, and the local context of rulean has at least the declarations of the C++ context. The test also gives three declarations to `lean_elab_add_decl` and `lean_elab_add_decl_without_checking` of the C++ kernel and of rulean, with a `Lean.Environment`. The verdicts, the exception and the new constants must be the same.

### 09.6.5 Trust in in-process mode

In-process mode is not covered by theorem T1 (10.1). The input comes from Lean objects, not from bytes. The conversion layer is in the hardened class (03.2). It is tested by running the whole Lean test suite and a full `lake build` of Mathlib with the rulean kernel, and by comparing every `addDecl` result with the C++ kernel in a dual-kernel build (11.3).

The test `tests/dual.rs` of `rulean-ffi` does this comparison in one process before the dual-kernel build is ready. It loads `libleanshared` of Lean v4.36.0, writes each test declaration as a `Declaration` object, and gives the same object to `lean_add_decl` of the C++ kernel and to rulean through the conversion of 09.6.3. The two verdicts must be the same. Then the test reads each new constant from the C++ environment with `lean_environment_find` and requires that it is the same constant as in rulean, with the same binder names and binder info. The CI job `ffi-runtime` runs the test on Linux.
