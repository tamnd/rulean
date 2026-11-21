# D. Runtime, file formats and the pure-Rust building blocks for rulean

Research date: 2026-11-21. Baseline toolchain: Lean v4.36.0 (released 2026-11-16), with
v4.37.0-rc1 (2026-11-18) changes flagged where they affect formats.
Release list: https://api.github.com/repos/leanprover/lean4/releases

Tags: **[P]** primary source (code, PR, official docs, crate tarball, measured data file) that
I read myself. **[S]** secondary (README claims, prior notes, search summaries) that I did not
re-check against code. **[U]** unverified, inferred or contested.

Abbreviations: `L436/...` = `https://github.com/leanprover/lean4/blob/v4.36.0/...`,
`L437/...` = `https://github.com/leanprover/lean4/blob/v4.37.0-rc1/...`,
`PR#n` = `https://github.com/leanprover/lean4/pull/n`, `I#n` = `https://github.com/leanprover/lean4/issues/n`.

---------------------------------------------------------------------------------------------

## 0. Release timeline relevant to formats

| Version | Date | Format-relevant change | Tag |
|---|---|---|---|
| v4.22.0 | 2025-08-14 | New LCNF compiler replaces old one (PR#8577) | [P] https://lean-lang.org/doc/reference/latest/releases/v4.22.0/ |
| v4.33.1 | 2026 summer | GMP >= 6.3.0 required (older GMP can give unsound results) | [P] L436/src/CMakeLists.txt lines 103-110 |
| v4.34.0 | 2026-09-14 | - | [P] releases API |
| v4.35.0 | 2026-10-12 | `Lean.ofReduceBool`/`reduceBool`/`trustCompiler` removed from kernel (PR#14953); Decidable becomes a structure (PR#8309); >255 ctor fields via spill objects (PR#15516) | [P] PR#14953, PR#15516 |
| v4.36.0 | 2026-11-16 | Current stable; olean v2/v3 | [P] releases API |
| v4.37.0-rc1 | 2026-11-18 | OLEAN_VERSION=4 single format (PR#16214); new 32-bit Expr hash mixer (PR#16107); big-Nat literal hash (PR#16146) | [P] PR#16214, PR#16107, PR#16146 |

Consequence: any binary reader must be version-gated. Format churn happened in 3 of the last
4 releases. [P]

---------------------------------------------------------------------------------------------

## 1. Where the kernel sits

### 1.1 Entry points (Lean side)

- `Lean.Kernel.Environment.addDeclCore` is declared in Lean as
  `@[extern "lean_add_decl"] opaque addDeclCore (env : Kernel.Environment) (maxHeartbeat : USize)
  (maxRecDepth : USize) (decl : @& Declaration) (cancelTk? : @& Option IO.CancelToken) :
  Except Kernel.Exception Kernel.Environment`. [P] L436/src/Lean/Environment.lean
- `@[extern "lean_add_decl_without_checking"]` variant exists for `debug.skipKernelTC`. [P] same file
- Elaborator path: `Lean.Environment.addDeclCore` -> `@[extern "lean_elab_add_decl"]`, implemented
  in `src/library/elab_environment.cpp`, which unwraps the elaborator `Environment` to the
  kernel environment and calls `environment::add`. [P] L436/src/Lean/AddDecl.lean, L436/src/library/elab_environment.cpp
- Other kernel externs reachable from Lean: `lean_kernel_is_def_eq`, `lean_kernel_whnf`,
  `lean_kernel_check` (used by `Kernel.isDefEq`, `Kernel.whnf`, `#reduce (kernel)`-style tools). [P] L436/src/Lean/Environment.lean
- C++ kernel calls back into Lean via `@[export]` functions: `lean_environment_find`,
  `lean_environment_add`, `lean_environment_mark_quot_init`, `lean_kernel_record_unfold`,
  diagnostics getters/setters. [P] L436/src/kernel/environment.cpp
- `environment::add` dispatches on `Declaration` ctor: axiomDecl, defnDecl, thmDecl, opaqueDecl,
  quotDecl, mutualDefnDecl, inductDecl. [P] L436/src/kernel/environment.cpp (307 lines)
- Async/parallel: elaborator uses `addConstAsync`; the elaborator `Environment` carries
  `checked : Task Kernel.Environment`; kernel environments are threaded linearly. [P] L436/src/Lean/Environment.lean

### 1.2 Kernel.Exception (must be reproduced exactly for a drop-in)

`unknownConstant, alreadyDeclared, declTypeMismatch, declHasMVars, declHasFVars, funExpected,
typeExpected, letTypeMismatch, exprTypeMismatch, appTypeMismatch, invalidProj,
thmTypeIsNotProp, other (msg), deterministicTimeout, excessiveMemory, deepRecursion,
interrupted`. Most carry `(env : Kernel.Environment) (lctx : LocalContext)` plus exprs. [P] L436/src/Lean/Environment.lean

### 1.3 Declaration shapes (input of the kernel)

[P] L436/src/Lean/Declaration.lean
- `ConstantVal {name : Name, levelParams : List Name, type : Expr}`
- `AxiomVal {.., isUnsafe : Bool}`; `DefinitionVal {.., value, hints : ReducibilityHints, safety : DefinitionSafety, all : List Name}`
- `ReducibilityHints = opaque | abbrev | regular (h : UInt32)`; `DefinitionSafety = unsafe | safe | partial`
- `TheoremVal {.., value, all}`; `OpaqueVal {.., value, isUnsafe, all}`; `QuotVal {.., kind}`
- `InductiveVal {numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive}`
- `ConstructorVal {induct, cidx, numParams, numFields, isUnsafe}`
- `RecursorVal {all, numParams, numIndices, numMotives, numMinors, rules : List RecursorRule{ctor, nfields, rhs}, k, isUnsafe}`
- `Declaration = axiomDecl | defnDecl | thmDecl | opaqueDecl | quotDecl | mutualDefnDecl (List DefinitionVal) | inductDecl (lparams) (nparams) (types : List InductiveType) (isUnsafe)`
Note: in .olean files `ConstantInfo` (post-kernel) is stored, not `Declaration`; recursors and
constructors are therefore *given* in oleans and must be re-derived by a checker, never trusted.
[P] L436/src/Lean/Environment.lean (ModuleData.constants : Array ConstantInfo)

### 1.4 Size of what is being replaced (v4.36.0 tarball, `wc -l`)

| Directory | Lines | Notes | Tag |
|---|---|---|---|
| src/kernel | 7,556 | type_checker.cpp 1,292; inductive.cpp 1,405; level.cpp 527; expr.cpp 476; instantiate.cpp 250; environment.cpp 307 | [P] |
| src/runtime | 18,061 | object.cpp 3,005; io.cpp 1,671; mpz.cpp 1,113; mpn.cpp 356; plus mimalloc, libuv glue, openssl.cpp, cadical.cpp | [P] |
| src/library | 5,898 | ir_interpreter.cpp 1,245; module.cpp; elab_environment.cpp; llvm.cpp; dynlib.cpp | [P] |
| src/util | 3,006 | name.cpp etc. | [P] |
| src/include | 3,839 | lean.h 3,813 | [P] |
| Lean sources (Init/Std/Lean/Lake) | 735,472 | | [P] |
| stage0/stdlib generated C | 12,661,651 | | [P] |
| `@[extern` occurrences | 1,013 | in Init/Std/Lean/Lake | [P] |
| `implemented_by` occurrences | 189 | | [P] |

Source: https://github.com/leanprover/lean4/archive/refs/tags/v4.36.0.tar.gz (counted locally).
The kernel proper is ~7.6 kLOC C++; the runtime + compiler + stdlib that "runs Lean programs"
is two orders of magnitude larger. [P]

---------------------------------------------------------------------------------------------

## 2. Lean object model (lean.h, v4.36.0)

Source for all of section 2: L436/src/include/lean/lean.h [P] unless noted.

### 2.1 Header (8 bytes, little-endian on all supported targets)

```c
typedef struct {
    int      m_rc;          // bytes 0..4
    unsigned m_cs_sz:16;    // bytes 4..6  (object byte size for small objects / compacted)
    unsigned m_other:8;     // byte 6      (num_objs for ctors; elem size for sarray; flags)
    unsigned m_tag:8;       // byte 7
} lean_object;
```
- `m_rc > 0`: single-threaded, non-atomic RC. `m_rc < 0`: multi-threaded, atomic RC (counting
  downward). `m_rc == 0`: persistent object (globals, compacted .olean regions); never freed. [P]
- Sticky RC band (RC-overflow fix, v4.35 PR#15288 family): `LEAN_RC_STICKY = INT_MIN+0x10000000`,
  `LEAN_RC_STICKY_DROP = INT_MIN+0x20000000`, `LEAN_RC_INC_MAX = 0x10000`; `lean_inc_ref` ->
  `lean_inc_ref_n(o,1)`; dec: `rc>1` -> plain sub, else `rc!=0` -> `lean_dec_ref_cold`. [P]
- `LEAN_LINEAR_MARK_MASK 0x80` in `m_other` (markLinear, PR#15052). [P]
- Comment in lean.h: during deletion, `m_rc` + `m_cs_sz` are reused as a 48-bit pointer for the
  deletion work-list; this is why ARM MTE/HWASAN tagged pointers are unsupported (I#13113). [P]
- mimalloc is the default allocator (`USE_MIMALLOC ON`); PR#14948 set `MI_MAX_ALIGN_SIZE=8`
  so a `List.cons` cell is 24 bytes. [P] L436/src/CMakeLists.txt, PR#14948

### 2.2 Tags

| Tag | Meaning |
|---|---|
| 0..243 | constructor objects (`LeanMaxCtorTag 243`) |
| 244 Promise, 245 Closure, 246 Array, 247 StructArray, 248 ScalarArray, 249 String, 250 MPZ, 251 Thunk, 252 Task, 253 Ref, 254 External, 255 Reserved | |

`LEAN_MAX_CTOR_NUM_OBJS 255`, `LEAN_MAX_CTOR_SCALARS_SIZE 1023`. PR#15516 (v4.35) allows
structures with >255 object fields by chaining spill objects; each runtime object still has
<=255 pointer fields. [P]

### 2.3 Scalars, ctor objects, arrays, strings

- Boxed scalars: `lean_box(n) = (n<<1)|1`; pointers are 8-aligned so bit 0 distinguishes. Small
  `Nat` is boxed if it fits (`LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1`, i.e. 2^63-1 on 64-bit, lean.h line 1670); otherwise an MPZ object. [P]
- Nullary constructors of an inductive with non-nullary siblings are `lean_box(cidx)`. [P]
- Ctor object: `header(8) | lean_object* objs[num_objs] | scalar area`. Scalars are addressed
  as `lean_ctor_get_uint64(o, num_objs*8 + off)`; usize fields come before other scalars;
  remaining scalars sorted by size descending. [P]
- `lean_array_object`: `header | size_t m_size @8 | size_t m_capacity @16 | lean_object* m_data[] @24`. [P]
- `lean_sarray_object` (ByteArray, FloatArray): `header | m_size @8 | m_capacity @16 | uint8 m_data[] @24`; element size in `m_other`. [P]
- `lean_string_object`: `header | size_t m_size @8 (bytes incl. NUL) | m_capacity @16 | m_length @24 (UTF-8 code points) | char m_data[] @32`. [P]
- MPZ (GMP build): `header | __mpz_struct {int _mp_alloc; int _mp_size (sign = sign of size); mp_limb_t* _mp_d}`; in compacted regions the limbs follow inline and `_mp_d` is relocated. Non-GMP build: `m_sign, m_size, m_digits`. The olean header flag bit0 records which. [P] L436/src/runtime/object.h, L436/src/runtime/compact.cpp
- Trivial structures (exactly one relevant field) are represented by that field: e.g.
  `FVarId`/`MVarId` are stored directly as a `Name` pointer inside `Expr.fvar`. [P] L436/src/kernel/expr.h line 236 (`fvar_name` = `cnstr_get_ref(e,0)` cast to `name`)

---------------------------------------------------------------------------------------------

## 3. Name, Level, Expr: concrete in-memory/olean layout

All derived from Prelude/Expr/Level definitions plus the C++ accessors. [P] for field order,
[U] where a byte offset is my arithmetic from the layout rules (marked "calc").

### 3.1 Name

[P] L436/src/Init/Prelude.lean lines 4874-4900; L436/src/util/name.h line 46
- `anonymous` = `lean_box(0)` (scalar; C++ `name()` = `box(name_kind::ANONYMOUS)`).
- `str (pre : Name) (str : String)`: tag 1, objs `pre @8, str @16`, computed `hash : UInt64 @24`. Size 32 (calc).
- `num (pre : Name) (i : Nat)`: tag 2, objs `pre @8, i @16` (boxed or MPZ), `hash @24`. Size 32 (calc).
- Hash: `anonymous -> 1723`; `str p s -> mixHash p.hash s.hash`; `num p v -> mixHash p.hash (v if v < 2^64 else 17)`.
  `String.hash` = `lean_string_hash` = MurmurHash64A-style `hash_str(len, bytes, 11)`;
  `mixHash` = `lean_uint64_mix_hash` (m = 0xc6a4a7935bd1e995, r = 47). [P] L436/src/runtime/hash.h, L436/src/include/lean/lean.h

### 3.2 Level

[P] L436/src/Lean/Level.lean; L436/src/kernel/level.h lines 63-72; L436/src/kernel/level.cpp line 516
- Ctors: `zero` (0), `succ l` (1), `max l1 l2` (2), `imax l1 l2` (3), `param n` (4), `mvar id` (5).
- Every ctor including `zero` carries a computed `data : UInt64`, so `zero` is a heap ctor object
  (0 objs + 8 scalar bytes), not a boxed scalar (C++ `g_level_zero = lean_level_mk_zero(..)`, persistent).
- `Level.Data`: bits 0-31 hash; bit 32 hasMVar; bit 33 hasParam; bits 40-63 depth (24 bits).

### 3.3 Expr

[P] L436/src/Lean/Expr.lean; L436/src/kernel/expr.h lines 123-257
Ctor indices: bvar 0, fvar 1, mvar 2, sort 3, const 4, app 5, lam 6, forallE 7, letE 8, lit 9, mdata 10, proj 11.
The computed `data : UInt64` sits immediately after the object fields:
`get_data(e) = lean_ctor_get_uint64(e, lean_ctor_num_objs(e)*8)`.

| Ctor | Object fields (offset) | data @ | extra scalar | size (calc) |
|---|---|---|---|---|
| bvar | idx:Nat @8 | 16 | - | 24 |
| fvar | FVarId(=Name) @8 | 16 | - | 24 |
| mvar | MVarId(=Name) @8 | 16 | - | 24 |
| sort | Level @8 | 16 | - | 24 |
| const | Name @8, List Level @16 | 24 | - | 32 |
| app | fn @8, arg @16 | 24 | - | 32 |
| lam / forallE | binderName @8, binderType @16, body @24 | 32 | binderInfo u8 @40 | 48 |
| letE | declName @8, type @16, value @24, body @32 | 40 | nonDep u8 @48 (`4*8+8`, expr.h line 256) | 56 |
| lit | Literal @8 (`natVal n` tag 0 / `strVal s` tag 1) | 16 | - | 24 |
| mdata | MData(KVMap) @8, expr @16 | 24 | - | 32 |
| proj | typeName @8, idx:Nat @16, struct @24 | 32 | - | 40 |

`BinderInfo`: default 0, implicit 1, strictImplicit 2, instImplicit 3. [P] Expr.lean

`Expr.Data` bits [P] L436/src/Lean/Expr.lean, L436/src/kernel/expr.cpp (`lean_expr_mk_data`):
- 0-31 hash (32 bits), 32-39 approxDepth (8 bits, saturates at 255), 40 hasFVar,
  41 hasExprMVar, 42 hasLevelMVar, 43 hasLevelParam, 44-63 looseBVarRange (20 bits).
- PR#8554/#8559 (2025-05): overflow of looseBVarRange/depth in data produced unsoundness;
  now saturating, max looseBVarRange 2^20-2. [P] https://github.com/leanprover/lean4/pull/8559

### 3.4 Hashing changes in v4.37.0-rc1 (the cached data in oleans changes meaning)

- PR#16107 (merged 2026-10-30): Expr hash mixing switched to a 32-bit MurmurHash3_x86_32 block
  step (`k*=0xcc9e2d51; k=rotl(k,15); k*=0x1b873593; h^=k; h=rotl(h,13); h=h*5+0xe6546b64`);
  lam/forallE get distinct seeds (29/31), letE hashes `nonDep` (41/37), approxDepth no longer
  mixed. Fixed a quadratic kernel slowdown (n=80,000 test: 2,746 G -> 8.56 G instructions).
  A 64-bit hash was evaluated and rejected: +17% olean size (+984 MB on Mathlib), +3.5% memory,
  +1% CPU. [P] PR#16107
- PR#16146 (merged 2026-11-12): `Literal` hash now covers all bits of big Nat literals (test with
  powers 65536^i, n=8000: 1.18 s -> 5.9 ms). [P] PR#16146
- Lesson for rulean: hashes and flags cached in `.olean` objects are (a) version-dependent and
  (b) attacker-controlled. A verified kernel must recompute them (or validate) on load. [P]+[U]

---------------------------------------------------------------------------------------------

## 4. Plugging a Rust kernel into Lean

### 4.1 Options

| Option | Mechanism | Pros | Cons | Tag |
|---|---|---|---|---|
| A. External checker | Read `.olean` (or lean4export NDJSON) in a separate process; report accept/reject | No FFI, no C++; how nanoda, lean4lean, nano-lean, con-ron, all Arena entries work; officially supported "external kernel" path (`lake check`, `leanchecker --from-export`, comparator) | Does not speed up `lake build`; only re-checks | [P] https://lean-lang.org/doc/reference/latest/External-Kernels/ |
| B. In-process replacement of `lean_add_decl` / `lean_elab_add_decl` | Rust `staticlib`/`cdylib` exporting `#[no_mangle] extern "C" fn lean_add_decl(env, max_hb: usize, max_rec: usize, decl: b_lean_obj_arg, cancel: b_lean_obj_arg) -> lean_obj_res`, linked into a custom Lean build instead of `src/kernel` | Speeds up every `lake build`; true drop-in | Must speak Lean RC/ownership ABI exactly; must call back `lean_environment_find/add` (Lean `@[export]` fns); must also provide `lean_kernel_is_def_eq/whnf/check` and keep C++ `library/` callers compiling (they include `kernel/*.h`), i.e. a thin C++ shim remains unless those are ported too | [P] for the entry points, [U] for effort |
| C. Symbol interposition (LD_PRELOAD / DYLD_INSERT_LIBRARIES) on `libleanshared` | Override `lean_add_decl` at load time | No Lean rebuild | Fragile, intra-library calls may be bound directly; macOS SIP; not shippable | [U] |
| D. Upstream a kernel-selection hook | Lean option selecting an alternative kernel via `@[extern]` indirection | Clean | Requires upstream buy-in | [U] |

### 4.2 ABI details that matter for option B

- `@&` = borrowed (callee must not dec); un-annotated = owned (callee consumes one ref). `env`
  is owned, `decl` and `cancelTk?` borrowed. Result is `Except` (ctor tag 0 = error, 1 = ok)
  allocated with `lean_alloc_ctor`. [P] lean.h, Environment.lean
- Objects reachable from the environment may be persistent (rc 0, inside mmapped regions),
  single-threaded or multi-threaded; Rust code must use `lean_inc/lean_dec` semantics including
  the sticky band, or never retain Lean objects (convert to its own representation). [P]
- Heartbeats (`maxHeartbeat`) and `IO.CancelToken` polling must be honoured to return
  `deterministicTimeout` / `interrupted`, otherwise behaviour differs from C++. [P]
- Is a Rust cdylib with `extern "C"` "C/C++"? It is Rust code using the C *calling convention*;
  no C source is compiled. Writing `#[repr(C)]` mirrors of `lean_object` (as `lean-sys` does) is
  pure Rust. However the `static inline` functions of lean.h (`lean_inc_ref`, `lean_alloc_ctor`,
  ...) are not exported symbols and must be re-implemented in Rust (lean-sys does exactly this). [P] https://crates.io/crates/lean-sys (0.0.9, 2025-09-24, 145,963 downloads)

---------------------------------------------------------------------------------------------

## 5. The .olean format (2026)

Sources: L436/src/library/module.cpp, L436/src/runtime/compact.cpp, L437/src/library/module.cpp, PR#16214. [P]

### 5.1 Header (v4.36.0)

```c
struct olean_header {              // packed, 88 bytes
  char   marker[5] = "olean";      // @0
  uint8  version;                  // @5   2 = plain, 3 = with closures (v4.36)
  uint8  flags;                    // @6   bit0: 1 = GMP mpz encoding, 0 = native mpz
  char   lean_version[33];         // @7   e.g. "4.36.0", NUL padded
  char   githash[40];              // @40  Lean commit; must match the reader
  size_t base_addr;                // @80  address the region was laid out for
};
```
- v2: object data follows at @88; the first 8 bytes of data are the root-pointer slot
  (compactor allocates it first). [P]
- v3: `size_t data_size @88`, data @96, then `u32 num_closure_offsets`, `u64 offsets[]`,
  `u32 num_libs`, entries `(size_t base, u32 len, id)` for closures pointing into shared libs. [P]
- v4.37.0-rc1 (PR#16214, merged 2026-11-17): `OLEAN_VERSION = 4`, one layout:
  `[header 88][data_size @88][root @96][objects...][u32 0 closures][u32 0 libs]`; reading v2 removed. [P]

### 5.2 Base address and loading

- `base_addr` = hash(module Name) mod 0x7f0000000000, aligned to 64 KiB (`1<<16`); `.ir` parts
  use `mainModule ++ `ir` for a distinct address. [P] module.cpp
- Load: `mmap(base_addr, MAP_PRIVATE, PROT_READ|PROT_WRITE)` (+`MAP_FIXED_NOREPLACE` on Linux). If
  the address is unavailable: malloc + read + relocation walk over all objects (`region_reader`). [P]
- Objects inside the region have `m_rc = 0` and `m_cs_sz` = object byte size, so the region can be
  walked linearly. [P] compact.cpp
- Compactor deduplicates by pointer identity and with a `max_sharing_table` (structural; strings
  hashed with `hash_str` and compared with `memcmp`). [P] compact.cpp
- Writer writes to a temp file and renames atomically. [P]
- Windows regression with `FILE_MAP_COPY` since v4.31.0-rc1: I#15644. [P]

### 5.3 Validation status

- No structural validation of oleans: I#16542 "Malformed .olean input can crash the importer"
  (closed 2026-11-18). lean4checker documentation states it trusts that oleans are structurally
  well-formed. [P] I#16542, https://github.com/leanprover/lean4checker
- Hence any rulean olean reader that is part of the trusted base must be a bounds-checked parser
  (offsets within region, tags valid, field counts match the expected ctor, acyclicity/topological
  order) rather than a pointer cast. [U] (design inference)

### 5.4 Module data and the module system

- `ModuleData {isModule, imports : Array Import, constNames : Array Name, constants : Array
  ConstantInfo, extraConstNames : Array Name, entries : Array (Name x Array EnvExtensionEntry)}`. [P] L436/src/Lean/Environment.lean
- Module system (`module` keyword): `writeModule` saves parts with one shared compactor via
  `saveModuleDataParts`: `X.olean` (exported), `X.olean.server`, `X.olean.private`, plus `X.ir`
  (and `X.ir.sig`). Later parts contain pointers into earlier parts (cross-region), so load order
  `.olean` -> `.olean.server` -> `.olean.private` is mandatory. `OLeanLevel = exported | server | private`. [P] L436/src/Lean/Environment.lean, L436/src/library/module.cpp
- In the exported part, theorems appear as `axiomInfo` (statement only) and non-exposed
  definitions have no body. A checker that only reads `X.olean` would check nothing about proofs;
  it must read `.olean.private`. [P] https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/
- Reference manual reports ~50% rebuild savings on Mathlib from the module system; Mathlib is
  migrating to `module` files (prior notes cite Mathlib PR #41950). [P] for manual, [S] for PR.
- `EnvironmentHeader {trustLevel, mainModule, isModule, imports, regions : Array CompactedRegion,
  modules, moduleNames}`. [P]

### 5.5 Sizes

- Mathlib oleans total ~5.8 GB (derived from PR#16107: +984 MB = +17%). [P]/[U] arithmetic
- Mathlib lean4export NDJSON: 5.9 GB, 112.1 M lines (Mathlib @ fc4f59e, Lean 4.36.0, export 3.1.0). [P] https://arena.lean-lang.org/results.json

---------------------------------------------------------------------------------------------

## 6. Existing non-C++ olean readers

| Project | Lang | Status | Notes | Tag |
|---|---|---|---|---|
| sdiehl/olean-export | Rust | crate `olean-export` 0.7.0, repo created 2026-10-04, pushed 2026-11-17, MIT | Reads olean v2 of Lean 4.26-4.35 "and refuses files from any other release"; emits lean4export NDJSON or "BLean" binary; cone export, per-module incremental export; README: Mathlib (4.35.0, 712,205 decls) 18 s vs lean4export 1,526 s (85x), peak 4.3 GB vs 9.4 GB. Deps include blake3, malachite-nz 0.6, memmap2, rayon, hashbrown, rustc-hash, xxhash-rust, optional mimalloc, libc; `unsafe_code = "deny"` | [P] repo/README https://github.com/sdiehl/olean-export ; perf [S] |
| digama0/leangz (leantar) | Rust | v0.1.22-pre1 supports v4 oleans; bundled with Lean toolchains/Mathlib cache | Olean (de)compressor; must understand full object graph and reconstruct hashes - best existing reference implementation of the layout | [P] https://github.com/digama0/leangz |
| digama0/olean-rs | Rust | 2019 | Lean 3 only | [P] |
| Dicklesworthstone/franken_lean | Rust | created 2026-07-21, 43 stars | README written "as if realized"; claims full toolchain rewrite, own bignum; has `fln check-olean`, `olean inspect` | [S]/[U] https://github.com/Dicklesworthstone/franken_lean |
| erwijet/oleander | Rust | 2022 | outdated | [S] |

---------------------------------------------------------------------------------------------

## 7. lean4export (text interchange format)

Source: https://lean-lang.org/doc/reference/latest/External-Kernels/ and https://github.com/leanprover/lean4export [P]
- Format version 3.1.0; NDJSON, one object per line. First line meta:
  `{"meta":{"exporter":{"name","version"},"lean":{"githash","version"},"format":{"version"}}}`.
- Three interning tables by id key: names `"in"` (0 = anonymous), levels `"il"` (0 = zero),
  exprs `"ie"`. Ids must be defined before use and exactly once.
- Name: `{"str":{"pre":i,"str":s},"in":k}` / `{"num":{"pre":i,"i":n},"in":k}`.
- Level: `succ`, `max`, `imax`, `param`.
- Expr: `bvar`, `sort`, `const{name,us}`, `app{fn,arg}`, `lam`/`forallE{name,type,body,binderInfo}`,
  `letE{name,type,value,body,nondep}`, `proj{typeName,idx,struct}`, `natVal` (decimal string),
  `strVal`, `mdata` (stripped unless `--export-mdata`).
- Decls: `axiom`, `def{hints: "opaque"|"abbrev"|{"regular":n}, safety, all}`, `opaque`, `thm`,
  `quot{kind}`, `inductive{types, ctors, recs}` (inductive block given with its ctors and recursors;
  checkers must regenerate and compare).
- lean4export tags up to v4.36.0-rc1, last push 2026-10-14. [P] GitHub API
- Toolchain integration (v4.34-v4.36): `lake check` (PR#14990), comparator `--paranoid`
  (PR#15145), `leanchecker --from-export` (PR#15050), hardened-allocator `leanchecker-paranoid`
  (PR#14884), kernel in a separate process for comparator (PR#15055), bubblewrap sandbox
  (PR#15005), streamed export (PR#15096). [P] PR pages
- Mathlib export is 5.9 GB (section 5.5); the official checker's own Mathlib time is dominated by
  checking, not parsing (see 12.3). [P]

---------------------------------------------------------------------------------------------

## 8. Compiler, runtime and "running" Lean programs

### 8.1 Pipeline

- Elaborated defs -> LCNF (new compiler, default since v4.22.0, PR#8577; IR built from LCNF since
  v4.21.0, PR#8211) -> IR (`Lean.IR`) -> EmitC (C, compiled by the bundled clang) or EmitLLVM
  (LLVM 23.1.0 bump, PR#14531). [P] release notes v4.21.0/v4.22.0, PR#14531
- `#eval`, macros, tactics, elaborators of the *current* package run through the IR interpreter
  (`src/library/ir_interpreter.cpp`, 1,245 lines), which calls native code for anything already
  compiled (imported packages, `@[extern]`). v4.36 fixes in the interpreter: PR#15493, PR#15539. [P]
- `@[extern "sym"]` binds a Lean constant to a C symbol (1,013 uses in core); `@[implemented_by f]`
  swaps the compiled implementation (189 uses). Both are invisible to the kernel: the kernel sees
  the Lean definition (or an `opaque` constant). [P]
- Runtime C/C++ dependencies today: GMP (>= 6.3.0), mimalloc, libuv (async IO, timers, TCP),
  OpenSSL (runtime/openssl.cpp), CaDiCaL (in-process SAT FFI for `bv_decide`, PR#15247), plus
  libc++/libstdc++ and the C code emitted for every compiled Lean module. [P] L436/src/runtime/, L436/src/CMakeLists.txt

### 8.2 native_decide and the kernel after v4.35

- PR#14953 (merged 2026-08-28, shipped v4.35.0) removed `Lean.reduceBool`, `Lean.reduceNat`,
  `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and kernel support for invoking
  the compiler (deprecated since 2026-02-01). [P] PR#14953
- `native_decide` now: `Lean.Meta.nativeEqTrue` compiles an auxiliary `_native.<tac>.decl`,
  evaluates it via `evalConst Bool`, then adds an **axiom** `_native.<tac>.ax : decl = true`.
  The kernel never executes compiled code; trust shows up in `#print axioms`. [P] L436/src/Lean/Meta/Native.lean
- Recommended validation ladder in the manual: blue check -> `#print axioms` -> `lean4checker
  --fresh` -> comparator `--paranoid`. [P] https://lean-lang.org/doc/reference/latest/ValidatingProofs/
- Consequence: a kernel that must "check every Lean program" needs no interpreter or codegen.
  Kernel-relevant extensions are only: Nat literal GMP-accelerated ops (`Nat.succ/add/sub/mul/div/
  mod/gcd/beq/ble/land/lor/xor/shiftLeft/shiftRight/pow`, `pow` guarded by a max exponent size
  `g_nat_max_size`), String literal expansion to constructors (`string_lit_to_constructor`),
  quotients, eta for structures, proof irrelevance. [P] L436/src/kernel/type_checker.cpp

### 8.3 Rust projects around the Lean runtime/compiler

| Crate/repo | Version / date | What | Tag |
|---|---|---|---|
| lean-sys | 0.0.9, 2025-09-24, 145,963 dl | Rust bindings to lean.h; re-implements static inline functions in Rust | [P] https://crates.io/crates/lean-sys |
| leo3 / leo3-ffi | 0.3.1, 2026-08-02 | Lean<->Rust FFI (PyO3-style) | [S] crates.io |
| lean-rs-host | 0.10.1, 2026-11-20 | embedding Lean in Rust hosts | [S] crates.io |
| lustc | 0.7.0, 2026-02-16 | compiles a Lean 4 subset to Rust source | [S] crates.io |
| O6lvl4/lean4-rust-backend | pushed 2026-03-07 | IR -> Rust backend with a Rust runtime (README unavailable, 404) | [U] GitHub search |
| argumentcomputer/ix | active, pre-alpha | zk proof-carrying code for Lean 4; Rust crates (aiur, ixon, ixvm-codegen, ...) incl. CUDA; benchmarks incl. FLT kernel | [S] https://github.com/argumentcomputer/ix |
| oxilean-kernel | 0.1.5, 2026-11-13 | Rust Lean-like kernel crate | [S] crates.io |

None of these is a production replacement for the C runtime. A full Rust runtime would need
~1,000 `@[extern]` primitives, Task/Thunk/Promise semantics, libuv-equivalent IO, and a backend
emitting Rust or machine code. [P] for counts, [U] for the effort assessment.

---------------------------------------------------------------------------------------------

## 9. Pure-Rust building blocks

Versions from the crates.io API on 2026-11-21; C usage from inspecting the published `.crate`
tarballs (build.rs and *.c/*.h/*.S files). [P] https://crates.io/api/v1/crates/<name>

### 9.1 Big integers (needed for Nat literal reduction)

| Crate | Version | License | Repr | C? | Tag |
|---|---|---|---|---|---|
| malachite (-nz, -base) | 0.14.0 (2026-10-13) | **LGPL-3.0-only** | `Natural(InnerNatural)`, `enum {Small(u64), Large(Vec<u64>)}`; FFT mult; build.rs only sets an `fft_avx2` cfg | pure Rust | [P] tarball src/natural/mod.rs:40-47, build.rs |
| num-bigint | 0.5.1 (2026-07-05) | MIT/Apache-2.0 | `BigUint { data: Vec<u64> }` (no inline small case) | pure Rust | [P] tarball |
| dashu (dashu-int 0.4.1) | 0.6.2 (2026-10-02) | MIT/Apache-2.0 | union inline 2 words / heap | pure Rust | [P] tarball src/repr.rs |
| ibig | 0.3.6 (2022-09-17) | MIT/Apache-2.0 | superseded by dashu | pure Rust | [P] |
| rug / gmp-mpfr-sys | - | LGPL | links GMP (C + asm) | **C** | [P] |

Benchmarks (tczajka/bigint-benchmark-rs, Xeon w7-3565X, updated 2026-10-14), seconds:

| Library | e 100k | e 1m | e 10m | fib 10m | fib 100m | fib_hex 100m |
|---|---|---|---|---|---|---|
| malachite 0.14.0 | 0.008 | 0.130 | 1.854 | 0.154 | 2.071 | 0.242 |
| rug 1.30.0 (GMP) | 0.008 | 0.146 | 2.440 | 0.165 | 2.782 | 0.483 |
| dashu 0.4.2 | 0.019 | 0.497 | 10.324 | 0.609 | 14.500 | 2.798 |
| num-bigint 0.4.6 | 0.019 | 0.582 | 18.261 | 0.741 | 23.821 | 5.430 |
| ibig 0.3.6 | 0.019 | 0.602 | 19.094 | 0.759 | 25.171 | 5.193 |

[P] https://github.com/tczajka/bigint-benchmark-rs (README). Note these are huge-number
workloads; kernel Nat literals are overwhelmingly < 2^64, where an inline fast path (u64 with
overflow check) matters far more than asymptotics. [U] (inference; check Mathlib literal
distribution). GMP 6.3.0 bug history (Lean requires >= 6.3.0 because older versions could give
unsound results) is an argument for a small, verified, own bignum for kernel use. [P] CMakeLists.txt

### 9.2 Hashing

| Crate | Version | License | C? | Notes | Tag |
|---|---|---|---|---|---|
| foldhash | 0.2.0 (2025-08-23) | Zlib | no | hashbrown's default hasher; README: geometric mean 6.21 ns (foldhash-f) vs fxhash 7.56, ahash 8.74, SipHash 28.70 (Xeon 8481c); `HashMap<u32,u32>` 40 B vs ahash 64, fx 32; output not stable across versions | [P] README in tarball |
| rustc-hash (FxHasher) | 2.1.3 (2026-07-03) | MIT/Apache | no | v2 is a new algorithm (not the old fxhash); deterministic | [P] crates.io |
| fxhash | 0.2.1 (2017) | | no | unmaintained | [P] |
| ahash | 0.8.12 (2025-05-08) | MIT/Apache | no (build.rs only sets cfgs) | AES-based when available; random state | [P] tarball build.rs |
| xxhash-rust | 0.8.21 (2026-11-15) | BSL-1.0 | no | pure Rust xxh3/xxh64 | [P] |
| blake3 | 1.8.7 (2026-08-20) | CC0/Apache | **yes by default**: build.rs uses `cc` to compile `c/blake3_*.c` and `.S` asm on x86/ARM; feature `pure` disables | [P] tarball build.rs lines 8-336 |

For a kernel, keys are mostly already-hashed terms or 32-bit handles; an identity/one-multiply
hasher over the cached structural hash is typically best. Deterministic hashing is preferable for
reproducible verification runs. [U]

### 9.3 Concurrent maps, arenas, interning

| Crate | Version | License | Notes | Tag |
|---|---|---|---|---|
| dashmap | 6.2.1 (2026-05-17) | MIT | sharded RwLock<HashMap>; pure Rust | [P] |
| papaya | 0.2.5 (2026-08-21) | MIT | lock-free, read-optimized, incremental resize, predictable latency (README) | [P] tarball README |
| scc | 3.9.1 (2026-11-20) | Apache-2.0 | HashMap/HashIndex/TreeIndex, SIMD lookup; repo moved to Codeberg | [P] |
| hashbrown | 0.17.1 (2026-10-13) | MIT/Apache | SwissTable; raw-entry/HashTable API for custom hash-consing | [P] |
| bumpalo | 3.20.4 (2026-11-13) | MIT/Apache | bump arena, `collections` feature | [P] |
| typed-arena | 2.0.2 (2023-01-09) | MIT | typed arena, stable/unmaintained | [P] |
| hashconsing | 1.8.0 (2026-10-08) | MIT/Apache | Arc-based hash-consing with global tables | [P] |
| internment | 0.8.6 (2026-08-20) | MIT/Apache | `Intern<T>` (leaks), `ArcIntern<T>` | [P] |
| string-interner | 0.20.0 (2026-04-30) | MIT/Apache | | [P] |
| rayon (-core) | 1.12.0 / 1.13.0 (2026-04-14) | MIT/Apache | work-stealing; build.rs only for `links` uniqueness | [P] tarball build.rs |
| parking_lot(_core) | 0.13.0 / 0.9.12 | MIT/Apache | build.rs only detects TSan | [P] tarball build.rs |
| crossbeam | 0.8.5 (2026-09-05) | MIT/Apache | | [P] |
| memmap2 | 0.9.12 (2026-10-21) | MIT/Apache | depends on `libc` crate (bindings, not C code) | [P] |
| rkyv | 0.8.18 (2026-08-05) | MIT | zero-copy archives; candidate for a rulean-native cache format | [P] |
| zerocopy / bytemuck | 0.8.64 / 1.25.2 | | safe transmutes for parsing headers | [P] |

Observed practice in the fastest Arena kernels: hand-written hash-consing into per-constructor
arrays with 32-bit handles (con-ron), bump arenas + hashbrown + rustc-hash (nano-lean),
no dependencies at all (Palladium). [P] Arena checker descriptions, repo Cargo.toml files.

### 9.4 Allocators

| Crate | Version | C? | Tag |
|---|---|---|---|
| mimalloc / libmimalloc-sys | 0.1.52 / 0.1.49 (2026-05-22) | **yes**: vendors `c_src/mimalloc` and compiles it with `cc` | [P] tarball |
| tikv-jemallocator (-sys) | 0.7.0 (2026-05-25) | **yes**: builds jemalloc C via configure/make | [P] crates.io |
| snmalloc-rs | 0.7.6 | **yes** (C++) | [P] |
| rpmalloc | 0.2.2 (2021) | **yes** (C) | [P] |
| talc | 5.1.1 (2026-09-09) | pure Rust, no_std-oriented | [P] |
| rlsf | 0.2.3 (2026-07-27) | pure Rust TLSF | [P] |
| std `System` | - | wraps libc malloc / HeapAlloc | [P] |

nano-lean and gruszka (optional) use mimalloc; a strict "no C" policy excludes it. Arena-style
kernels can avoid most malloc pressure with arenas, making the system allocator adequate. [P]/[U]

### 9.5 JSON (only needed for lean4export input)

| Crate | Version | C? | Notes | Tag |
|---|---|---|---|---|
| serde_json | 1.0.154 | no (build.rs sets cfgs) | baseline | [P] |
| simd-json | 0.19.0 (2026-10-27) | no C files in tarball; SIMD intrinsics | simdjson port | [P] |
| sonic-rs | 0.5.12 (2026-11-19) | no C files; Rust SIMD (sonic-simd) | ByteDance | [P] |

The lean4export grammar is tiny and fixed; a hand-written NDJSON scanner (as kefir/nanoda/nano-lean
use with memchr) is simpler to verify than a general JSON library. A binary interchange
(olean-export "BLean", gruszka's "Susz") removes JSON parsing from the critical path. [P]/[U]

---------------------------------------------------------------------------------------------

## 10. Does Rust "contain C"? (scoping the "no C/C++" requirement)

- Rust `std` on Linux-gnu links glibc dynamically and, by default, `libgcc_s` for unwinding;
  `-Clink-self-contained`/`+crt-static` link LLVM's libunwind (C/C++) shipped in the std component.
  [P] https://rust-lang.github.io/rfcs/3873-build-std-context.html
- The pre-built std enables `compiler_builtins/c`, i.e. some compiler-rt **C** intrinsics are
  compiled into the shipped std on Linux/Fuchsia. [P] RFC 3873 ("It is enabled for the pre-built
  standard library")
- macOS: the only stable syscall interface is libSystem; Go moved to libSystem in Go 1.11 for this
  reason. [P] https://go.dev/doc/go1.11 ; Windows: kernel32/ntdll + UCRT. [S]
- Libc-free Rust exists only on Linux: `rustix` 1.1.6 (linux_raw backend) + `linux-raw-sys`
  0.12.1, `origin` 0.26.2, `eyra` 0.22.0 (2025-04-30), `c-scape`/`c-gull` 0.22.3 (2026-02-21).
  Last eyra release is 2025-04; niche. [P] crates.io
- `panic = "abort"` removes the unwinder dependency; `-Z build-std` (nightly) can drop the
  compiler-rt C intrinsics. [P] RFC 3873/3874 https://rust-lang.github.io/rfcs/3874-build-std-always.html
- Crates in this survey that compile C/asm at build time: blake3 (default), libmimalloc-sys,
  tikv-jemalloc-sys, snmalloc-rs, rpmalloc, rug/gmp-mpfr-sys. Crates with a build.rs that does
  **not** compile C: malachite-nz, ahash, rayon-core, parking_lot_core, serde_json, zerocopy. [P] tarball inspection
- Recommended policy check in CI: `cargo tree -e build` + deny any crate depending on `cc`,
  `cmake`, `bindgen`, `pkg-config`; `cargo deny` bans list; plus scan vendored sources for
  `*.c|*.cc|*.cpp|*.h|*.S|*.asm`. [U] (proposal)

---------------------------------------------------------------------------------------------

## 11. Ecosystem scale and test corpora

### 11.1 Repositories (GitHub API, 2026-11-21) [P]

| Repo | Stars | Size (KB) | Last push | Notes |
|---|---|---|---|---|
| leanprover-community/mathlib4 | 4,513 | 503,511 | 2026-11-21 | 2026-10-25 stats: 291,178 theorems, 139,569 defs, 9,437 files, 2,481,682 lines [S] prior notes / mathlib stats page |
| leanprover-community/batteries | 437 | 30,173 | 2026-11-20 | |
| leanprover/cslib | 823 | 15,968 | 2026-11-20 | Arena export incl. deps: 2.3 GB / 44.1 M lines [P] |
| anthropics/fermats-last-theorem | 1,322 | 232,567 | 2026-09-24 | ~13 M lines, written by Claude Aug 7-17, announced Sep 4 [S] prior notes |
| ImperialCollegeLondon/FLT | 1,061 | 39,701 | 2026-11-18 | human-led FLT project |
| leanprover/lean-kernel-arena | 60 | 3,535 | 2026-11-21 | |
| ammkrn/nanoda_lib | 243 | 7,120 | 2026-11-07 | Rust, Apache-2.0 |
| digama0/lean4lean | 279 | 1,416 | 2026-10-10 | |
| leanprover/comparator | 249 | 111 | 2026-10-14 | |

- RH project (Levent Alpöge, alpo.ge): toolchain v4.33.1, 175,187 modules, ~17.5 M total lines
  (Development library 12,374,591), ~1,060,800 declarations, longest import chain 203,
  archive 239,275,554 bytes. [S] /Users/apple/notes/Spec/2148r/01-research.md (not re-verified)
- Tau Ceti ~3 M lines [S] prior notes.
- Scale implication: AI-generated corpora are already 5-7x Mathlib in lines; checker throughput
  and memory per declaration, not per-term cleverness, will dominate. [U]

### 11.2 Lean Kernel Arena (current round, data timestamp 2026-11-21 01:41 UTC)

Source: https://arena.lean-lang.org/ and https://arena.lean-lang.org/results.json (9.2 MB),
repo https://github.com/leanprover/lean-kernel-arena [P]
- 37 registered checkers; test tarball: 135 good + 90 bad tests (7.8 MB, excluding >10 MB tests);
  large tests: mathlib (5.9 GB, Lean 4.36.0), cslib (2.3 GB), navier-stokes-euler (OpenAI repo,
  1.5 GB, Lean 4.34.0-rc2), cedar (863 MB), con-leche (669 MB), std (557 MB), init (332 MB),
  reachability (18 MB); groups `bugs/` (30), `corner-cases/` (expected outcome "either"),
  `perf/`, `tutorial/`. [P]
- Time metric "virtual CPU" = instructions / 6.0 Ginstr/s (sums over threads). [P]
- "official" = `leanchecker --from-export` from v4.35.0. [P] results.json checker `run` field

Mathlib test, selected rows (wall s / cpu s / peak RSS / instructions), runs dated 2026-11-19..21: [P]

| Checker | Lang | Threads | Wall | CPU | RSS | Instr | vs official instr |
|---|---|---|---|---|---|---|---|
| official v4.35.0 (C++) | C++ | 1 | 2,696 | 2,696 | 10.6 GB | 1.210e13 | 1x |
| official-nightly 2026-11-14 | C++ | 1 | 2,575 | 2,575 | 10.7 GB | 9.816e12 | 1.23x |
| nano-lean v0.4.2 (sdiehl) | Rust | 4 | 50 | 167 | 5.4 GB | 3.951e11 | 30.6x |
| gruszka (NbE, Susz binary input) | Rust | 4 | 32 | 110 | 2.6 GB | 5.135e11 | 23.6x |
| sokonanoda (closures, smalltt-style) | Rust | - | 54 | 178 | 5.3 GB | 5.275e11 | 22.9x |
| mathgraph (sokonanoda fork) | Rust | - | 179 | 344 | 6.6 GB | 9.122e11 | 13.3x |
| pestka (Aver -> Rust) | Aver | 4 | 148 | 503 | 3.7 GB | 1.702e12 | 7.1x |
| kefir (low-memory, streaming) | Rust | 1 | 430 | 430 | 2.7 GB | 2.582e12 | 4.7x |
| palladium (no deps) | Rust | 4 | 162 | 648 | 4.2 GB | 2.831e12 | 4.3x |
| nanoclo | Rust | - | 256 | 827 | 7.9 GB | 3.011e12 | 4.0x |
| con-ron (port of verified con-leche) | Rust | 4 | 178 | 551 | 4.7 GB | 3.474e12 | 3.5x |
| nanobruijn | Rust | - | 405 | 1,248 | 7.4 GB | 4.707e12 | 2.6x |
| nanoda | Rust | - | 442 | 1,475 | 6.4 GB | 5.775e12 | 2.1x |
| con-leche (Lean, consistency proof vs ZFC model) | Lean | 4 | 206 | 801 | 5.2 GB | 6.135e12 | 2.0x |

- All of the above accept all 145 good tests they attempt and reject all bad tests they attempt
  (no `incorrect` rows for these checkers in results.json); con-ron/con-leche/sokonanoda/palladium
  decline 3 bad tests. Corner cases (`either`) differ between checkers (e.g. eta for structures,
  imax normalization, alg-conv transitivity with Quot/Acc). [P] results.json
- con-agua: con-leche re-implemented at x86-64 assembly level, compiled by a verified compiler,
  with a ~200-line C harness (a "verified + fast" data point; 10.9 min virtual CPU, 11.6 GB). [P] Arena description
- lean4lean, kiota, ocaml4lean, logos-kernel etc. do not finish Mathlib in the current round. [P]

---------------------------------------------------------------------------------------------

## 12. Implications for rulean

### 12.1 What "run every Lean program" should mean

1. **Must**: rulean accepts exactly the declarations the official kernel accepts, for every
   `.olean` (incl. `.olean.server`/`.olean.private` parts) and every lean4export 3.x stream
   produced by any Lean program. Rejection behaviour must be at least as strict (all Arena
   `bad/` tests rejected). Measured on: Init/Std/Lean, Batteries, Mathlib, CSLib, FLT (both),
   Arena suite, and one AI-scale corpus (RH or Anthropic FLT). [P]-based recommendation
2. **Should (phase 2)**: drop-in in-process kernel (option B in section 4.1): Rust staticlib
   exporting `lean_add_decl`, `lean_add_decl_without_checking`, `lean_kernel_is_def_eq`,
   `lean_kernel_whnf`, `lean_kernel_check`, identical `Kernel.Exception` values, heartbeat and
   cancellation semantics, so that every Lean program (elaborator, tactics, `lake build`) runs
   unchanged with rulean as its kernel.
3. **Out of scope**: re-implementing the Lean compiler, IR interpreter, or C runtime in Rust.
   Since v4.35 (PR#14953) the kernel never executes compiled code; `native_decide` yields an
   explicit `_native.*` axiom that rulean should report (and optionally refuse) exactly like
   `#print axioms`. Interpreting the requirement as "execute every Lean program" would mean
   replacing ~1,000 `@[extern]` primitives, Task/IO runtime, libuv, GMP, CaDiCaL and the C backend,
   which is a different, much larger project than a kernel. [P] counts; [U] judgement

### 12.2 What "10x faster than the C++ kernel" means in practice

- On the Arena Mathlib export, existing Rust checkers already use 23-31x fewer instructions than
  `leanchecker --from-export` v4.35.0 (nano-lean 3.95e11 vs 1.21e13) and finish in 32-54 s wall on
  4 threads vs 2,696 s. 10x is therefore *already demonstrated* for external checking; rulean's
  benchmark must be specified precisely: baseline (official stable vs nightly, which is ~1.23x
  better), metric (instructions vs wall, threads), input (export vs olean, incl. parse time),
  and corpus. Recommend: Arena methodology (instruction count, Mathlib export) plus an olean-input
  run and an in-process `lake build` kernel-time run. [P] results.json
- The hard part is "10x **and** formally verified": the fastest verified-lineage entry today
  (con-ron, Rust port of con-leche) is 3.5x; con-leche itself 2.0x. [P]

### 12.3 Format handling recommendations

- Implement an olean reader for v2, v3 (closures table) and v4 (v4.37+) headers, version-gated on
  `lean_version`+`githash`, with per-release layout tables (the hashes in `Expr.Data` changed in
  v4.37 via PR#16107/#16146). [P]
- Never trust cached `Expr.Data`/`Level.Data`/`Name.hash` or given recursors/ctors from files;
  recompute (the kernel needs its own hash anyway). Treat oleans as untrusted input (I#16542):
  bounds-checked parsing, no `MAP_FIXED` at the file's `base_addr`, translate pointers as offsets
  relative to `base_addr`, resolve cross-part pointers (.olean -> .server -> .private). [P]+[U]
- Support lean4export NDJSON 3.1.x as the reference interchange (used by Arena and `lake check`);
  consider a binary interchange only as an optimization. [P]
- Reuse knowledge, not necessarily code, from digama0/leangz (complete object-graph handling, v4
  support) and sdiehl/olean-export (Rust, `unsafe_code = "deny"`, but MIT and v2-only today). [P]

### 12.4 Recommended interpretation of "no C/C++"

- **Strict and checkable**: no C/C++/assembly source in the rulean tree or compiled by any
  dependency's build script (ban `cc`, `cmake`, `bindgen`, `pkg-config` in the build graph; no
  vendored `*.c/*.h/*.S`). Enforce with `cargo deny` + a CI scan. [U] proposal
- **Acceptable**: linking the platform system library (glibc/musl, libSystem on macOS, UCRT on
  Windows) through Rust std and the `libc` crate, and the compiler-rt intrinsics that ship inside
  Rust's std; there is no portable way to avoid them (macOS has no stable syscall ABI). Document
  them as "platform TCB" outside the verification claim. Use `panic = "abort"` to drop the
  unwinder. Optional Linux-only "zero libc" build via rustix/origin is possible but not worth
  making a requirement. [P] RFC 3873, Go 1.11 notes
- **The C ABI is not C**: exporting `extern "C"` functions from a Rust staticlib/cdylib for
  integration with the (C++) Lean binary is compatible with the rule; the Lean process itself
  remains C/C++ and is not part of rulean's TCB. [P]/[U]

### 12.5 Crates: recommended / avoid

Recommended (pure Rust, permissive): `hashbrown` 0.17 (HashTable API for hash-consing),
`rustc-hash` 2.1 or `foldhash` 0.2 (but prefer a deterministic custom hasher over cached term
hashes), `bumpalo` 3.20 or own typed arenas, `rayon` 1.12, `parking_lot` 0.13, `crossbeam` 0.8,
`papaya` 0.2 or `dashmap` 6 for shared environment lookups (or avoid concurrency in the trusted
core and parallelize per-declaration over an immutable environment), `memmap2` 0.9 (read-only
mapping, never at fixed address), `zerocopy`/`bytemuck` for header parsing, `num-bigint` 0.5 as a
fallback bignum, `smallvec`, `memchr`. [P] versions/licences

Bignum: write a small own `Nat` (inline u64 fast path + Vec<u64> limbs, schoolbook/Karatsuba
and Knuth division), proven or differentially tested against `num-bigint` and `malachite`.
`malachite` 0.14 is fastest (beats GMP in bigint-benchmark-rs) but is **LGPL-3.0-only** and a
very large dependency (2,588 files in malachite-nz alone) - fine as a test oracle, risky as a TCB
dependency. `dashu` is the permissive middle ground. [P]

Avoid in the trusted/shipped build: `mimalloc`/`libmimalloc-sys`, `tikv-jemallocator`,
`snmalloc-rs`, `rpmalloc` (all C/C++), `rug`/`gmp-mpfr-sys` (GMP), `blake3` without
`features = ["pure"]` (compiles C + asm by default), anything using `cc`/`bindgen`. Use
`talc`/`rlsf` or the system allocator plus arenas if a custom allocator is needed. `serde_json`,
`simd-json`, `sonic-rs` are pure Rust but unnecessary for a fixed grammar; a hand-written
NDJSON scanner is smaller and easier to verify. [P]

### 12.6 Open questions for the spec

- Which Lean versions must be supported simultaneously (v4.36 stable + v4.37 rc already differ in
  olean version and hash function)? [P]
- Must rulean reproduce the C++ kernel's behaviour on Arena "corner-cases" (where checkers already
  disagree, e.g. struct-eta corner cases, alg-conv transitivity), or only on soundness-relevant
  tests? [P] results.json
- Is in-process integration (option B) a hard requirement or a phase-2 goal? It forces matching
  Lean's object ABI (RC sticky band, persistent objects, ownership) inside the verified boundary,
  or a conversion layer outside it. [U]
