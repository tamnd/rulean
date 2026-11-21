# A. The official Lean 4 kernel: source, semantics, incidents, checkers, arena (research as of 2026-11-21)

Scope: the facts rulean needs in order to (a) accept exactly what the official kernel accepts, (b) beat it by 10x, and (c) be verified.
This replaces section 1.2 ("Kernels and the 2026 soundness incidents", "Comparator", "Versions") of `Spec/2148/01-research-2026.md`. That section was verified claim by claim; the audit is in section 9.

## 0. Conventions

- **[P]**: read from a primary source: source code, the GitHub API or issues, release notes, an author's own blog, or raw arena JSON.
- **[S]**: secondary source only, such as a search-engine summary, a third-party blog or an aggregator.
- **[U]**: unverified, contested, or my own inference.
- **`L/…`** is shorthand for `https://github.com/leanprover/lean4/blob/ab8894fb4de9405d7be3627bdcfbfe74be0383d0/…`. That commit is lean4 `master` as of 2026-11-21, "perf: split first more refuting discriminants in the match compiler (#16653)", version 4.38.0-dev. I read it from a shallow clone and did not build it.
- **`lean4#N`** is shorthand for `https://github.com/leanprover/lean4/issues/N` (GitHub redirects PR numbers there).
- **`T/<tag>/…`** means the same file at a release tag: `https://github.com/leanprover/lean4/blob/<tag>/…`.
- **Arena data**:
  - live results: https://arena.lean-lang.org/results.json, snapshot 2026-11-21 01:41 UTC, arena commit 2d6b1ff6, run 44849254431. Abbreviated **ARENA**.
  - Round 2026-09 results: https://zenodo.org/records/22944094, file `lean-arena-round-2026-09-results.json`. Abbreviated **ROUND**.
- **Blogs**:
  - **PM1**: https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/
  - **PM2**: https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/
  - **VK**: https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/
  - **WW**: https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/
- **Release notes**: **RN(x)** is `https://lean-lang.org/doc/reference/latest/releases/v<x>/`.

---

## 1. The official kernel source (C++, `src/kernel`)

### 1.1 File inventory: `wc -l` on master ab8894fb [P] (`L/src/kernel/`)

The 35 `.h`/`.cpp` files total **8,049 lines** (plus a 25-line CMakeLists.txt). `equiv_manager.{h,cpp}` no longer exists; #14806 replaced it with pair caches.

| File | Lines | Responsibility |
|---|---:|---|
| type_checker.cpp | 1303 | `infer_type`, `whnf`/`whnf_core`, `is_def_eq`, lazy delta, Nat/String literal extensions, eta, struct eta, unit-like, proof irrelevance |
| type_checker.h | 173 | The checker state: caches, `m_lparams`, `m_eager_reduce`, `definition_safety` |
| inductive.cpp | 1415 | `add_inductive`: uniformity, positivity, universe checks, nested elimination, recursor generation, `check_recursors` |
| inductive.h | 161 | `inductive_reduce_rec` (iota), `to_cnstr_when_K`, `to_cnstr_when_structure`, nat/string literal to constructor |
| environment.cpp / .h | 314 / 110 | `add_decl` dispatch, name/universe/fvar/mvar checks, `add_definition`/`theorem`/`opaque`/`mutual`, diagnostics |
| declaration.cpp / .h | 248 / 481 | `declaration`, `constant_info`, reducibility hints, `definition_safety` |
| level.cpp / .h | 527 / 198 | Universe levels: `mk_max`/`mk_imax` simplification, `normalize`, `is_equivalent`, `is_geq`, instantiate |
| expr.cpp / .h | 478 / 377 | Expr constructors (the Lean-side `Expr` is shared through the C ABI), `has_fvar`, loose bvar range |
| expr_eq_fn.cpp / .h | 308 / 18 | Structural equality, optionally comparing binder info, with a pointer-pair cache |
| instantiate.cpp / .h | 249 / 42 | `instantiate`, `instantiate_rev`, `instantiate_lparams`, `cheap_beta_reduce`, `head_beta` |
| abstract.cpp / .h | 69 / 16 | `abstract` (fvars to bvars) |
| replace_fn.cpp / .h | 196 / 184 | Cached replace traversal |
| for_each_fn.cpp / .h | 217 / 30 | Cached visitor traversal |
| find_fn.h | 27 | Find a subterm |
| local_ctx.cpp / .h | 105 / 93 | Local context: fvar decls, let-fvars |
| quot.cpp / .h | 123 / 99 | `add_quot`, plus `quot_reduce_rec` (Quot.lift and Quot.ind iota) |
| kernel_exception.h | 218 | 15 exception classes |
| ptr_pair_set.h | 75 | Pointer-pair hash set, used by the def-eq caches |
| trace.cpp / .h | 61 / 47 | Kernel tracing |
| expr_maps.h, expr_sets.h | 16 / 16 | Hash maps and sets keyed on expr |
| init_module.cpp / .h | 42 / 13 | Static initialisation |

`wc` was run on every file; this table merges .h/.cpp pairs. Line counts of `type_checker.cpp` at release tags [P] (`T/<tag>/src/kernel/type_checker.cpp`): v4.31.0 1244, v4.33.1 1373, v4.35.0 1330, v4.36.0 1292, v4.37.0-rc1 1303.

### 1.2 Runtime dependencies of the kernel: trusted, outside `src/kernel` [P]

| Dependency | File(s) and lines | Why the kernel needs it |
|---|---|---|
| Lean object model, refcounting | `L/src/runtime/object.h` (490), `object.cpp` (3120), `L/src/include/lean/lean.h` (3901) | Every `expr`, `level`, `name` is a Lean heap object. Refcounts are 32-bit; overflowing them was a soundness bug (#14838, #15241, #15288) |
| Bignums | `L/src/runtime/mpz.h` (327), `mpz.cpp` (1152), `mpn.cpp/h` | Nat literal arithmetic. Built on GMP (≥ 6.3.0 required since #14833) or on a native mpn fallback (`-DUSE_GMP=OFF`) |
| Hashing | `L/src/runtime/hash.h` (20), `hash.cpp` (61) | Expr hash, computed in Lean (`L/src/Lean/Expr.lean`, mixHash with per-kind seeds) |
| Sharing | `L/src/runtime/sharecommon.h` (70), `.cpp` (478) | `sharecommon_persistent` on theorem type/value. The overflow panic is #15289 |
| Compacted regions (.olean) | `L/src/runtime/compact.h` (148), `.cpp` (690), `L/src/library/module.cpp` (642) | Imported constants are mmapped, compacted, immortal objects |
| Lean-side wrapper | `L/src/Lean/Environment.lean`, `Declaration.lean`, `Expr.lean`, `Level.lean` | The `Expr`, `Level`, `Declaration` and `ConstantInfo` datatypes; `addDeclCore` FFI |

The `Expr` header data [P] (`L/src/Lean/Expr.lean`):
- a 32-bit hash, an 8-bit approxDepth, a 20-bit looseBVarRange, and flags (hasFVar, hasExprMVar, hasLevelMVar, hasLevelParam);
- mixHash seeds per kind: const 5, bvar 7, sort 11, fvar 13, mvar 17, mdata 19, proj 23, lam 29, forall 31.

Hashing of large Nat literals: #16146 now hashes all bits (lean4#16146). lean4#15686 reported that hashing modulo 2^64 made checking quadratic for literals that are multiples of 2^64; it was closed 2026-11-12 [P].

### 1.3 Declaration kinds, constant kinds, safety [P] (`L/src/kernel/declaration.h`, `L/src/Lean/Declaration.lean`)

| Enum | Values |
|---|---|
| `declaration` (input to `addDecl`) | Axiom, Definition, Theorem, Opaque, Quot (field-less), MutualDefinition, Inductive (a mutual group of types, each with constructors) |
| `constant_info` (stored) | Axiom, Definition, Theorem, Opaque, Quot (kind type/ctor/lift/ind), Inductive, Constructor, Recursor |
| `definition_safety` | unsafe, safe, partial |
| `reducibility_hints` | opaque, abbrev, regular(height: u32) |

How the hints compare (`compare` in `declaration.cpp`) [P]:
- Regular against Regular: unfold the one with the greater height, or both if the heights are equal.
- Abbrev is unfolded first.
- Opaque is unfolded last.
- Theorems get `opaque` hints from `get_hints`.

**Theorem unfolding [P, important]:**
- `declaration::has_value()` became `is_definition()` only in #12973 (2026-03-23, "theorems are opaque"; lean4#12973).
- But `constant_info::has_value()` still returns `is_theorem() || is_definition()`, and the kernel's `is_delta` uses that one.
- So the **kernel still delta-unfolds theorems**, with opaque hints, as a last resort.
- #12973 changed the elaborator side and `declaration.h` only. A reimplementation that refuses to unfold theorems will reject terms the official kernel accepts. [P by code reading; I did not run it.]

### 1.4 What `add_decl` checks [P] (`L/src/kernel/environment.cpp`)

Common checks:
- the name is not already declared;
- universe params have no duplicates;
- no mvars or fvars (fvars in opaque values since #14498, found by Patrick Hulin with GPT-5.6, lean4#14498);
- no loose bvars;
- all `level` params used are declared (`check_level`).

| Kind | Check |
|---|---|
| Axiom | The type is a type (`ensure_sort`) |
| Definition (safe/partial) | The type is a sort; the value is checked in an env **without** the decl, and `infer(value) ≡ type` |
| Definition (unsafe) | The header is added first, so recursion through the name is allowed. Unsafe constants are rejected when referenced from safe code |
| Theorem | `sharecommon_persistent`(type, value); `is_prop(type)`, meaning `ensure_sort(infer(type))` normalizes to 0 (#14807, #14613); value checked |
| Opaque | The value is checked against the type |
| MutualDefinition | Must be unsafe or partial; all share the same safety (#14608) and the same level params; no duplicate names (#14632) |
| Quot | `add_quot`; see 1.8 |
| Inductive | `add_inductive`; see 1.7 |

The FFI entry point is `lean_add_decl(env, max_heartbeat, max_rec_depth, decl, cancel_tk)`, exposed as `Lean.Kernel.Environment.addDeclCore` [P] (`L/src/Lean/Environment.lean` line 336). It wraps:
- `scope_restore_num_heartbeats`, which counts heartbeats per declaration since #16548 (lean4#16548);
- `scope_max_rec_depth` set to **16 × maxRecDepth** (#13956, lean4#13956);
- the cancel token.

`lean_add_decl_without_checking` is a trusted bypass. If an environment's trust level is above `LEAN_BELIEVER_TRUST_LEVEL` = 1024, declarations are added unchecked (`L/src/kernel/environment.h` lines 20–23).

### 1.5 Type checker state and caches [P] (`L/src/kernel/type_checker.h`)

| Cache | Key → value | Notes |
|---|---|---|
| `m_infer_type[2]` | expr → type; index = `infer_only` | Two tables, for check mode and infer-only mode |
| `m_whnf_core` | expr → expr | Used only when both `cheap_rec` and `cheap_proj` are false |
| `m_whnf` | expr → expr | Easy cases are not cached: BVar, Sort, MVar, Pi, Lit |
| `m_success` / `m_failure` | `expr_pair_set` | Before #14806 this was a union-find `equiv_manager`, which made results order-dependent and transitive although def-eq is **not** transitive (lean4#14806). `is_def_eq` caches successes only. `failed_before`/`cache_failure` is used only in the lazy-delta argument shortcut |
| `m_unfold` | (const, levels) → instantiated value | Caches universe-polymorphic unfoldings (#12259) |

Each `infer_type_core` and `is_def_eq_core` call runs `check_system` (heartbeat, interrupt, stack) and `scope_rec_depth` [P].

### 1.6 `whnf`, `whnf_core`, reduction [P] (`L/src/kernel/type_checker.cpp`, `inductive.h`, `quot.cpp`)

`whnf(e)` loops: `t1 = whnf_core(t)`. If `reduce_nat(t1)` succeeds, return the result. Otherwise, if `unfold_definition(t1)` succeeds, continue with it. Otherwise return `t1`. Results are cached.

`whnf_core(e, cheap_rec, cheap_proj)`:
- **Beta**: multi-argument, via `instantiate` of the body with the reversed args.
- **Zeta**: `let` substitutes the value; a let-fvar unfolds to its value.
- **Proj**: whnf the struct (or `whnf_core` when `cheap_proj`).
  - A string literal is first expanded to its constructor form.
  - Then, if it is a constructor app whose inductive equals `proj_sname` (this sname check is #14631), return `args[nparams+idx]`.
- **Iota**: if the head is a recursor, `inductive_reduce_rec`; if Quot.lift/Quot.ind, `quot_reduce_rec`.
- **mdata** is stripped.

`inductive_reduce_rec` (master, which matches v4.37.0-rc1) [P] (`L/src/kernel/inductive.h`):
1. major := the arg at `nparams+nmotives+nminors+nindices`.
2. If the recursor is K, `to_cnstr_when_K`: build the constructor app from the major's type, provided `infer(major) ≡ type(constructor)`.
3. `if (!is_prop(infer_type(major))) major = whnf(major)`. The guard is new in #15371 (v4.37.0-rc1). In v4.36.0 and earlier the major is always whnf-ed [P] (`T/v4.36.0/src/kernel/inductive.h`).
4. A nat literal becomes `Nat.zero` or `Nat.succ (n-1)`. A string literal becomes `whnf(String.ofList …)`.
5. Otherwise `to_cnstr_when_structure`: eta-expand the major for a non-recursive structure, unless the recursor is not large-eliminating. "Large-eliminating" is tested as: the recursor's lparam count equals the first type's lparam count (#15371).
6. Find the rule by constructor name. Check that the arg count is ≥ nparams + nfields.
7. The result is `instantiate_lparams(rule.rhs)` applied to: the first nparams+nmotives+nminors recursor args, then the last nfields args of the major, then the remaining extra args.

Quot [P] (`L/src/kernel/quot.cpp`): `Quot.lift f h (Quot.mk r a)` → `f a`, and `Quot.ind h (Quot.mk r a)` → `h a`. `Quot.mk` is found at arg 5 for lift and arg 4 for ind, whnf-ed, and must have exactly 3 args; f or h is arg 3 (`L/src/kernel/quot.h` lines 43–64).

### 1.7 Nat and String literal extensions: the exact operations [P] (`L/src/kernel/type_checker.cpp` lines 595–691)

- **Literal recognition** (`is_nat_lit_ext`): `Nat.zero` counts as literal 0. A `Lit` has type `Nat` or `String` (`infer_lit`).
- **Arity**: `Nat.succ` has 1 argument; every other op has exactly 2, and only fully applied apps reduce. Each argument is put through **`whnf`** (full, including delta) and must then be a literal.
- **Which constants**: the match is on the constant expressions `Nat.add` etc. **No check is made that those constants have the expected definitions.**
  - `lake check` therefore pins these names in the challenge: `primitiveTargets` lists Nat.add … Nat.shiftRight, String.ofList, Char.ofNat, List, eagerReduce, Nat, String, String.mk, Char, optParam, autoParam, semiOutParam, outParam.
  - Its comment: "the kernel makes no guarantees when fed other definitions here" [P] (`L/src/lake/Lake/CLI/Check.lean` lines 633–665).

| Op | Result | Size guard (`LEAN_NAT_MAX_SIZE`, default 128 MiB, #14849) |
|---|---|---|
| `Nat.succ n` | n+1 | Result size checked |
| `Nat.add`, `Nat.sub` (truncated), `Nat.mul` | GMP op | Result size checked |
| `Nat.pow b e` | b^e | e must be ≤ UINT_MAX (`get_count_arg`), else a kernel exception. Rejected if b>1 and size(b) > max/e |
| `Nat.gcd`, `Nat.div`, `Nat.mod` | GMP op, with Lean semantics for 0 | No check (results do not grow) |
| `Nat.beq`, `Nat.ble` | `Bool.true` / `Bool.false` constants | none |
| `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftRight` | Bitwise op | No check |
| `Nat.shiftLeft v s` | v·2^s | s ≤ UINT_MAX; size(v)+s/8+1 checked unless v=0 |

- **Not in the kernel**: Nat.log2, Nat.powMod (#13490 adds powMod as a *definition* using square-and-multiply, RN(4.35.0)), Nat.decEq, Int, Fin, UInt*, and anything native.
- **Literal size**: `infer_lit` also rejects literals above the bound.
- **`LEAN_NAT_MAX_SIZE`** is read once with `strtoull` at initialisation. A malformed value means the default.
- **Where `reduce_nat` fires**:
  - in `whnf`, always;
  - in `lazy_delta_reduction`, only if neither side has fvars **or** `m_eager_reduce` is set. `m_eager_reduce` is set by the `eagerReduce` identity hint (#9865, lean4#9865).
- **Bool reflection shortcut** (`is_def_eq_core`): if `s` is the constant `Bool.true` and (`t` has no fvars or eager_reduce is set), then `whnf(t) == Bool.true` gives true.
- **String**: `try_string_lit_expansion` compares a string `Lit` with an app of `String.ofList` by expanding the literal to `String.ofList [Char.ofNat n, …]`. This changed from `String.mk` in #10330 and #11048.
- **Removed in-kernel native reduction**: `Lean.reduceBool`, `reduceNat`, `ofReduceBool`, `ofReduceNat` and `trustCompiler` were removed in #14953 (2026-08-28, first shipped in **v4.35.0**). `native_decide` now asserts each native evaluation as an axiom (RN(4.35.0); lean4#14953) [P]. Tag check: still present in `T/v4.33.1/src/kernel/type_checker.cpp`, gone in v4.35.0 [P].

### 1.8 `is_def_eq_core`: exact order on master and v4.37.0-rc1 [P] (`L/src/kernel/type_checker.cpp` lines 1139–1214)

1. `quick_is_def_eq`:
   - pointer or structural equality, or `succeeded_before`;
   - Lam/Pi → `is_def_eq_binding` (domains defeq; bodies compared after instantiating a fresh fvar);
   - Sort → `is_equivalent` on levels;
   - MData → strip;
   - Lit → value equality.
2. The Bool.true shortcut (1.7).
3. **`is_def_eq_proof_irrel(t, s)` on the original terms**: if `infer(t)` is a Prop, the answer is `infer(t) ≡ infer(s)`. Since #15103 (v4.37.0-rc1) this runs *before* any whnf. In **v4.36.0 and earlier** it runs after step 4, on t_n and s_n [P] (`T/v4.36.0/src/kernel/type_checker.cpp`).
4. `t_n = whnf_core(t, cheap_rec=false, cheap_proj=true)`, and likewise for s. If either changed, quick check again.
5. `lazy_delta_reduction(t_n, s_n)` loops over:
   - `is_def_eq_offset` (Nat.zero, succ, literal);
   - `reduce_nat`, guarded as in 1.7;
   - `lazy_delta_reduction_step`:
     - compare hints; the side with the bigger height unfolds;
     - if one side is not a delta, try `try_unfold_proj_app` on the other first;
     - if both are the same regular definition, try `is_def_eq_args` plus level equality, unless `failed_before`; on failure, `cache_failure`;
     - unfolding uses `whnf_core(…, false, true)`;
     - the loop exits with DefEqual, DefDiff, DefUnknown or Continue.
6. Same constant with `is_def_eq` levels → true. Same fvar → true.
7. proj against proj with the same sname and idx → `lazy_delta_proj_reduction` on the structs.
8. `whnf_core` with full projection. If either side changed, recurse into `is_def_eq_core`.
9. `is_def_eq_app`: same arity, heads defeq, args defeq.
10. `try_eta_expansion`: a lambda against a non-lambda whose type whnfs to a Pi.
11. `try_eta_struct`:
    - the target is a non-recursive structure-like inductive (one constructor, zero indices);
    - the other side's type must be defeq;
    - the constructor app may be partial; partial-application eta is #15373 in v4.37.0-rc1.
12. `try_string_lit_expansion`.
13. `is_def_eq_unit_like`:
    - a non-recursive structure whose constructor has **0 fields**, and the types are defeq;
    - #15372 extended this to Pi types and proof/unit fields; it was merged and then **reverted** by #16443 on 2026-11-17 because of a +2.2% Mathlib instruction count. It is absent from v4.37.0-rc1 and master [P] (lean4#16443).
14. Otherwise false.

### 1.9 Typing rules worth pinning [P] (`L/src/kernel/type_checker.cpp`)

- **`infer_constant`**:
  - the level count must match;
  - in safe mode, unsafe and partial constants are rejected;
  - every level param must be in the declaration's params (`check_level`);
  - the result is `instantiate_lparams`.
- **`infer_lambda` / `infer_pi` / `infer_let`**: each binder type is checked before the context is extended (#14633). A let value must have a type defeq to the declared type (#10476). The result goes through `cheap_beta_reduce`. Pi results are `imax` of the sorts.
- **`infer_app`** (check mode): whnf the function type to a Pi; the argument type must be defeq to the domain.
- **`infer_proj`**:
  - whnf the struct's type;
  - the head must be a const equal to `proj_sname`, be an inductive with exactly 1 constructor, and have `nargs == nparams + nindices`; the idx must fit and be < nfields (2^32 aliasing fixed in #14632/#16279);
  - **if the struct's type is a Prop**: every earlier field that the result depends on must itself be a Prop, and the projected field must be a Prop (#14613: `Sort (imax 1 0)` must be recognised as Prop).
- **`is_prop(e)`** is `ensure_sort(whnf(infer(e)))` with a level that `normalizes_to_zero`. It must fail closed on stuck types (#14807, #14843).
- **Infer-only mode** skips argument and binder checks. The kernel uses it on recursor rules, `check_recursors` (#14808) and for theorem values [U on the exact call sites].

### 1.10 Levels [P] (`L/src/kernel/level.cpp`)

- **`mk_imax(u, v)`**:
  - if v is never zero (succ, or max with a never-zero part) → `max u v`;
  - `imax u 0 = 0`;
  - `imax 0 u = imax 1 u = u` (the `imax 1 u` case is #7631, 2025-05-21);
  - `imax u u = u`.
- **`normalize`**:
  - push succ inward;
  - flatten nested max;
  - sort args by `is_norm_lt`;
  - for each base, keep only the maximum offset;
  - drop explicit constants subsumed by an offset term.
- **`is_equivalent(l1, l2)`** is `l1 == l2` or `normalize(l1) == normalize(l2)`. **This is incomplete**: #14977 plans "complete level comparison".
- **`is_geq(l1, l2)`** is structural on normalized forms: max on the right means all; max on the left means any; imax and param are handled by cases. It is used for constructor field universes in `inductive.cpp`.
- **`normalizes_to_zero`** is used by `is_prop` and by inductive Prop detection.
- To match the official kernel, rulean must replicate *these algorithms*, not a complete decision procedure: a complete one accepts more. The arena corner cases `imax-nested-absorption` and `imax-right-successor` are rejected by the official kernel (ARENA).

### 1.11 Inductive types [P] (`L/src/kernel/inductive.cpp`, master)

1. **`check_uniform_ind_occs`** (#14582, merged 2026-08-12; raised by Arthur Adjedj): every occurrence of a type being declared must be applied to exactly the declaration's level params and the parameter bvars. Over-applied occurrences are descended into.
2. **`check_inductive_types`**:
   - every type has the same params, defeq;
   - `nindices` is counted after whnf of the type telescope;
   - the result sort must be the same for all types, compared with `is_equivalent` (#14615 normalizes, which widens acceptance).
3. **`check_constructors`**:
   - no duplicate names;
   - the params match;
   - each field's sort `l` satisfies `is_geq(result_level, l)`, or the result `normalizes_to_zero`;
   - strict positivity unless unsafe: an occurrence is allowed only as `Pi xs, I params idx` with no occurrence in `xs`;
   - `is_valid_ind_app`: the result has the exact params, and the indices do not mention the types being declared (#2125, 2023).
4. **No mvars, fvars or loose bvars** (#14607, #16512).
5. **Nested inductives**:
   - `elim_nested_inductive` builds auxiliary types named `_nested.*` (that prefix is reserved for user names, #14616);
   - the parametric args Ds of the nested occurrence are now type-checked (#14577, the #14576 fix);
   - `restore_nested` maps back; it throws instead of asserting (#14633), and the result is re-checked (#14621).
6. **`elim_only_at_universe_zero`** (large elimination), in order:
   1. the result level is not zero → false (large elim allowed);
   2. mutual → true;
   3. more than 1 constructor → true;
   4. 0 constructors → false;
   5. **recursive → true**. This is **new on master** (#13851, merged 2026-11-21 00:07 UTC, in no release yet). It removes `Acc.rec` large elimination; `Acc.rec'` is provided through `Classical.choice` with no iota;
   6. otherwise, every field that is not a Prop must occur in the result type's indices.
7. **K-like**: a single, non-mutual Prop inductive with one constructor that has zero fields → `k = true` (`Eq`).
8. **Recursor generation**: motives, minors with IHs, rules. **`check_recursors`** (#14808) type-checks the generated recursor types and rules.
9. **Sizes**: counts are `size_t`; #16279 fixed 32-bit truncation of numParams.

### 1.12 Quot [P] (`L/src/kernel/quot.cpp`)

- `add_quot` requires `Eq` to exist with exactly the expected shape: `Eq.{u} : {α : Sort u} → α → α → Prop`, one constructor `Eq.refl`.
- The four names `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` must be undeclared (#14632).
- It adds them with hard-coded types and sets `quotInit`.
- `Quot.sound` is an ordinary axiom from Init.
- #15023 (open) proposes `Quot : Sort (max 1 u)`.

### 1.13 `Kernel.Environment`, diagnostics and exceptions [P] (`L/src/Lean/Environment.lean`)

- **Environment split**: since #5145 (2025-01-18) there is `Lean.Kernel.Environment`, separate from the elaborator's `Environment`. Kernel checking has been asynchronous since commit bab10cc2b (2025-01-24).
- **Kernel environment fields**: `constants : ConstMap`; `quotInit`; `diagnostics : Diagnostics` (`unfoldCounter : PHashMap Name Nat`, `enabled`); `importedExtraConsts`; extension arrays; `header : EnvironmentHeader` (`trustLevel : UInt32`, `mainModule`, `isModule`, `imports`, `regions : Array CompactedRegion`, `modules`, `moduleNames`).
- **FFI**: `lean_add_decl`, `lean_add_decl_without_checking`, `lean_kernel_is_def_eq`, `lean_kernel_whnf`, `lean_kernel_check`. Unfold diagnostics go through `lean_kernel_record_unfold`. Diagnostics are only updated by `addDecl`.
- **Exceptions** (`L/src/kernel/kernel_exception.h`): unknown_constant, already_declared, definition_type_mismatch, declaration_has_metavars, declaration_has_free_vars, theorem_type_is_not_prop; with a local context: function_expected, type_expected, type_mismatch, def_type_mismatch, expr_type_mismatch, app_type_mismatch, invalid_proj; plus generic `kernel_exception(msg)`, deep recursion, and interruption/heartbeat.
- Only accept versus reject matters for rulean; the exception class is not part of acceptance.

### 1.14 Kernel-relevant commits, 2025–2026 [P] (`gh api repos/leanprover/lean4/commits?path=src/kernel`; each lean4#N)

| PR | Date | Change | Effect on acceptance |
|---|---|---|---|
| #5145 | 2025-01-18 | `Kernel.Environment` split | none |
| #8060 | 2025-04-23 | Nat.pow fix | fix |
| #7631 | 2025-05-21 | `imax 1 u` normalizes to `u` | widens |
| #8559 / #8560 | 2025-05-30 | Block exploit of a non-aborting `assert!` | narrows |
| #8751 | 2025 | letE `nondep` field | none |
| #9865 | 2025-08-12 | `eagerReduce` hint | widens (reduce_nat with fvars) |
| #9886 | 2025-08-13 | Reject Prop/Type-polymorphic inductives without subsingleton elimination | narrows |
| #10330, #11048 | 2025 | String literals via `String.ofList` | changes |
| #10476 | 2025 | `infer_let` value-type fix | narrows |
| #12259 | 2026 | Cache for universe-polymorphic unfolding | perf |
| #12973 | 2026-03-23 | Theorems opaque (elaborator `declaration::has_value`) | the kernel still unfolds theorems |
| #13956 | 2026-07-07 | Recursion limit 16 × maxRecDepth | resource |
| #14498 | 2026-07-22 | Check fvars in opaque values | narrows |
| #14577 … #14849 | 2026-07-28 → 08-19 | Bug-hunt fixes (section 2) | narrows; #14615 widens |
| #14953 | 2026-08-28 | Native reduction removed | narrows |
| #15103 | 2026-10-20 | Proof irrelevance before whnf | widens and perf; v4.37 |
| #15371 | 2026-10-20 | Eta-expand the major of subsingleton structures; no whnf of proof majors | widens; v4.37 |
| #15373 | 2026-10-20 | Eta for partial constructor applications | widens; v4.37 |
| #15372 → #16443 | 10-20 → 11-17 | Extended unit-like, then reverted | in nightly-2026-11-14, not in rc1 |
| #15928–#16107 | 10-25 → 10-30 | Perf work (hash bijection #16107) | perf |
| #16146 | 2026-11 | Hash all bits of big Nat literals | perf |
| #16279 | 2026-11-05 | size_t counts | narrows |
| #16512 | 2026-11-17 | Loose bvars in inductives | narrows; "benign" per RN(4.37.0) |
| #16548 | 2026-11-18 | Heartbeats per addDeclCore | resource |
| #13851 | 2026-11-21 | No large elimination for recursive Prop inductives (Acc) | **narrows**; master only |

### 1.15 Semantics by version: which official kernel to match [P] (tag files, ARENA)

| Feature | v4.31.0 | v4.32.2 | v4.33.1 | v4.35.0 | v4.36.0 | v4.37.0-rc1 | master |
|---|---|---|---|---|---|---|---|
| equiv_manager union-find | yes | yes | no | no | no | no | no |
| #14576 fix (nested Ds checked) | no | yes | yes | yes | yes | yes | yes |
| `check_uniform_ind_occs`, `check_recursors`, `LEAN_NAT_MAX_SIZE` | no | no | yes | yes | yes | yes | yes |
| reduceBool / reduceNat in the kernel | yes | yes | yes | **no** | no | no | no |
| Proof irrelevance before whnf_core | no | no | no | no | no | **yes** | yes |
| No whnf of proof majors; partial-constructor eta | no | no | no | no | no | **yes** | yes |
| Recursive Prop → no large elimination (Acc) | no | no | no | no | no | no | **yes** |

ARENA shows the drift directly. On the 30 "either" corner cases, official v4.35.0 and official nightly-2026-11-14 disagree on 8:
- eta-ctor;
- eta-struct-major-and;
- eta-struct-major-and-no-whnf and eta-struct-major-no-whnf (both time out at 60 s on v4.35.0);
- the four eta-unit-like-* cases;
- subject-reduction-redex.

The nightly's unit-like acceptances are #15372, which was later reverted. **Rulean must name a target version, such as v4.36.0, the latest stable.**

---

## 2. Soundness incidents

### 2.1 #14576 (CVE-2026-72844)

| Fact | Value | Tag and source |
|---|---|---|
| Title | "Kernel accepts wrong-structure projections, allowing an axiom-free proof of False" | [P] lean4#14576 |
| Reported | 2026-07-28 03:28Z by kiranandcode, on 4.34.0-nightly-2026-07-27; closed 13:39Z | [P] lean4#14576 |
| Origin | Ramana Kumar's AI-assisted "CollatzLean" disproof, published 07-25 (https://github.com/xrchz/CollatzLean) | [P] PM1 |
| Root cause | Phantom parameter args Ds of a nested occurrence vanish from the auxiliary type and escape type checking. Reachable only through metaprogramming (a raw `addDecl`). "implementation bug, not a hole in Lean's meta-theory" | [P] PM1 |
| Fix | #14577 by de Moura, opened 05:08Z (about 1.7 h after the report), merged 07-29 | [P] lean4#14577; openwall CVE post |
| First release with the fix | **v4.32.2 (2026-07-28)**, nightly-2026-07-29 | [P] RN(4.32.2), GitHub release API. The 08-02 advisory says no fixed stable release existed yet, which contradicts that date [U] |
| Affected | The CVE post says "Lean 4 ≤ v4.31.0 / nightly ≤ 2026-07-27". v4.32.0 (07-13) and v4.32.1 (07-22) came before the fix, so they must also be affected; the CVE text is inconsistent | [P] https://www.openwall.com/lists/oss-security/2026/10/26/2 ; [U] the v4.32.0/1 inference |
| CVSS | 3.1: 7.1 High; 4.0: 6.8 | [P] same post |
| Role of the hash collision | The PoC pads two Bool constants (`pad(false,78670)` against `pad(true,24083)`) until their hashes and approxDepth collide. "the means of reaching the flaw, not its cause"; "defeating kernel caching". The exact mechanism is not explained | [P] openwall 10/26/2 ; [U] mechanism |
| Other checkers | nanoda (a week old) accepted it because it "did not verify the type name in a projection node". lean4lean was affected (it ports the C++ code). leanchecker accepted it | [P] PM1; [P] https://www.openwall.com/lists/oss-security/2026/08/02/1 |
| Advisory | Jonathan Brossard, oss-security, 2026-08-02. Recommends "--trust=0" re-checks; notes the project has no SECURITY.md | [P] openwall 08/02/1 |
| Follow-ups | #14607/08/09/13/15/16; hardening #14621/31/32; comparator.live runs nanoda by default | [P] PM1 |

### 2.2 The bug hunt, 2026-07-30 to 08-20, shipped in v4.33.1 (2026-08-21) [P] PM2, RN(4.33.1)

| PR | Class | Bug | Found by or note |
|---|---|---|---|
| #14613 | kernel | `Sort (imax 1 0)` not recognised as Prop, so the `infer_proj` Prop guard was skipped | Rejected by nanoda and ind-models |
| #14616 | kernel | A user name with `_nested` plus `restore_nested` gives a universe change, then equiv_manager transitivity | Rejected by nanoda and ind-models |
| #14806 | kernel | equiv_manager union-find made def-eq order-dependent; used to build a recursor whose type and rule disagree | Rejected by nanoda and ind-models |
| #14807 (+#14843 in inductive.h, #14847 test) | kernel | `is_prop` returned false on a stuck type instead of failing | Daniel Selsam (OpenAI). **nanoda accepted** the bogus proof, ind-models rejected it, lean4lean was not affected |
| #14582 | kernel | Non-uniform occurrences of the inductive being defined | nomeata; raised by Arthur Adjedj; co-authored by Claude |
| #14808 | kernel | Type-check generated recursors | hardening |
| #14838 | runtime | 32-bit refcount overflow (needs ≥ 18 GB RAM); objects are now frozen, Koka-style sticky | runtime-soundness label |
| #14833 | runtime | Portable Linux releases shipped GMP 6.1.2; GMP ≥ 6.3.0 is now required | "could not rule out … other similar exploits based on GMP 6.3.0" |
| #14849 | runtime | No bound on Nat numeral size; now 128 MiB | runtime-soundness |
| #14161 | infra | TSan | none |

The PM2 counts: "5 soundness PRs, 2 runtime-soundness PRs, 5 other PRs".
- New GitHub labels: `soundness` (3 PRs: #14806, #14807, #14843) and `runtime-soundness` (5 PRs: #14833, #14838, #14849, #15241, #15289) [P] (GitHub search API, label filters).
- Quote: "`lake build` does not protect users from adversarial proofs" [P] PM2.

### 2.3 Later runtime-soundness fixes, in v4.35.0 [P] RN(4.35.0)

- #15241: deletion cascades released frozen objects (use-after-free, extended to False).
- #15289: `sharecommon_quick_fn` count wrap; inputs over 100 GB.
- #15288: UB when a heavily shared object crosses threads.
- "Kernels that are not based on the Lean runtime were not affected."
- Non-GMP mpz bugs: #15945, #15950. #11485 zeroes mpz padding in oleans. #16213 adds compactor allocation checks.

### 2.4 The blog posts

- **WW**, "Who watches the provers", 2026-03-16 [P]: Claude Opus 4.6 found 7 Rocq kernel bugs and 2 nanoda bugs, and no false proof in Lean; mentions a 2022 big-number arithmetic bug in Lean fixed within 24 h; the arena then had 7 kernels and 133 benchmarks; "nanoda is under 5,000 lines of Rust".
- **PM1** (2026-08-01) and **PM2** (2026-08-24) are summarised above.
- **VK**, "Lean now ships with verified kernels", 2026-10-15 [P]: four extra kernels ship (nanoda, lean4lean, con-leche, con-ron). con-leche is "the first kernel for Lean written in Lean and proven consistent" (set-theoretic model, following Carneiro), runs at "0.69x the instructions of the official kernel", and "checks the whole library in about 100 seconds using eight threads". con-ron is Rust, refined to con-leche via Aeneas. lean4lean verification is "expected … in the next few months". The sandbox opt-out is `--inadvisably-no-sandbox`. "We need binary export formats and incremental checking with external checkers."
- **Hales**, guest post on Tao's blog, 2026-10-09 (https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/) [S, via a search summary]: about 25 Lean kernels; "As of October, 2026, I know of no complete, public relative-consistency proof covering Lean abstract type theory"; wants a clean-room kernel; warns that AI could plant backdoor bugs.

### 2.5 Historical (pre-2026) kernel soundness issues [P unless marked]

| Issue | Year | Summary |
|---|---|---|
| lean4#2125 | 2023-02 | Self-referential indices in inductives gave unsoundness; fixed next day (`is_valid_ind_app`) |
| 2022 bignum bug | 2022 | Big-number arithmetic bug, fixed within 24 h [S] WW (no PR number found) |
| lean4#8559, #8560 | 2025-05 | Adversarial exploit of a non-aborting `assert!` in release builds |
| lean4#9886 | 2025-08 | Overly conservative recursors for Prop/Type-polymorphic inductives |
| lean4#2258 | 2023 → closed 2026-10-20 | Def-eq transitivity failure for unit-like eta (completeness, not soundness) |
| lean4#12520 (open) | 2026-02 | Def-eq transitivity failure for function eta |
| lean4#7637 (open) | 2025-03 | Projections versus sort polymorphism |

---

## 3. Releases, cadence, roadmap

Dates are GitHub release publish dates [P] (`gh api repos/leanprover/lean4/releases`):

| Release | Date | Kernel-relevant content |
|---|---|---|
| v4.28.0 | 02-16 | none |
| v4.29.0 | 03-27 | #12973 elaborator side |
| v4.28.1 / v4.29.1 | 04-14 | none |
| v4.30.0 | 05-26 | none |
| v4.31.0 | 06-15 | none |
| v4.32.0 / v4.32.1 | 07-13 / 07-22 | Affected by #14576 [U] |
| **v4.32.2** | 07-28 | #14576/#14577 fix (RN(4.32.2)) |
| v4.33.0 | 08-10 | none |
| **v4.33.1** | 08-21 | All bug-hunt fixes (RN(4.33.1)) |
| v4.34.0 / v4.34.1 | 09-14 / 09-24 | none |
| **v4.35.0** | 10-12 | `lake check`, `--paranoid`, `leanchecker --from-export`, native reduction removed, `Decidable` a structure, runtime fixes |
| v4.36.0-rc1 / rc2 | 10-14 / 10-27 | none |
| **v4.36.0** | **11-16** | No kernel semantic change versus v4.35.0; only fixes to kernel-rejected `grind`/`sym` proofs (RN(4.36.0)) |
| **v4.37.0-rc1** | **11-18** | #15103, #15371, #15373, #16279, #16512; #14892: WF definitions now depend on `Classical.choice` (RN(4.37.0)) |

The old notes gave v4.31.0 as 06-13; GitHub's publish date is 06-15 [P]. The roughly monthly cadence holds.

**v4.35.0 details** [P] RN(4.35.0): `lake check`, which "replays the export through the kernel, and fails if anything uses an axiom other than the standard ones" (#14990); `--paranoid` (#15145) "accepts the project only if every one of them does"; `leanchecker-paranoid` with a hardened allocator (#14884); `leanchecker --from-export` (#15050); `--from-export` for lake check and lake comparator (#15157); a bubblewrap sandbox with the kernel in a separate process, Linux only (#15005, #15055); bundled checkers (#15048, #15099, #15130, #15153); a sandbox-disable flag (#15156); `Decidable` stores "a `Bool` together with a proof" (#8309); `Nat.powMod` (#13490); mimalloc `MI_MAX_ALIGN_SIZE=8` (#14948).

**FRO roadmap, Year 4 Part 1 (Sep 2026–Feb 2027)** (https://lean-lang.org/fro/roadmap/y4-1/) [P], Trust section: "External checking must become a routine part of every Lean user's workflow"; `lake check`, `lake check <kernel>`, `--paranoid`; "We will include comparator in the Lean distribution"; "a mode where `lake build` skips the official kernel checks and only produces oleans"; continuing the #14576 postmortem actions (hardening, collaboration with AI research teams, supporting new external kernels). There is no item on kernel performance or on verifying the C++ kernel.

**Kernel renovation meta-issue** lean4#14977 (open, 2026-08-31, Adjedj and Breitner) [P]: complete level comparison; explicit inductive feature flags (impredicativity, projections, eta, K, large elimination); Quot of Prop in Type (#15023); Prop structures with non-Prop fields lose projections; sort-polymorphic large elimination (#7637); no rec rules for Prop-only recursors; a bundled release together with a new ndjson format; #15374 (partial recursor eta) pending. **This is a moving target: plan for versioned semantics.**

---

## 4. Toolchain around the kernel

### 4.1 lean4export NDJSON, format 3.1.0 [P] (https://github.com/leanprover/lean4export, `format_ndjson.md`; last push 2026-10-14; also in core as `L/src/LeanExport/Basic.lean` (474 lines) and `Parse.lean` (533 lines))

- **Line 1**: `{"meta":{"exporter":{name,version},"lean":{githash,version},"format":{"version":"3.1.0"}}}`.
- **Names** (`in` index; anonymous is the implicit 0): `{"str":{"pre":i,"str":s},"in":k}`, `{"num":{"pre":i,"i":n},"in":k}`.
- **Levels** (`il` index; zero is the implicit 0): `succ:i`, `max:[i,j]`, `imax:[i,j]`, `param:nameIdx`.
- **Exprs** (`ie` index):
  - `bvar:n`, `sort:levelIdx`, `const:{name,us[]}`, `app:{fn,arg}`;
  - `lam` / `forallE`: `{name,type,body,binderInfo: default|implicit|strictImplicit|instImplicit}`;
  - `letE:{name,type,value,body,nondep}`, `proj:{typeName,idx,struct}`;
  - `natVal:"<decimal string>"`, `strVal:s`, `mdata:{expr,data}`.
- **Declarations**:
  - `axiom{name,levelParams,type,isUnsafe}`;
  - `def{…,value,hints:"opaque"|"abbrev"|{"regular":n},safety:"unsafe"|"safe"|"partial",all}`;
  - `opaque{…,value,isUnsafe,all}`;
  - `thm{…,value,all}`;
  - `quot{name,levelParams,type,kind:"type"|"ctor"|"lift"|"ind"}`;
  - `inductive{types[],ctors[],recs[]}` with these fields:
    - InductiveVal: numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive;
    - ConstructorVal: induct, cidx, numParams, numFields;
    - RecursorVal: all, numParams, numIndices, numMotives, numMinors, rules `{ctor,nfields,rhs}`, k.
- **Exporter behaviour** [P] (`Export.lean`):
  - structural dedup through a HashMap;
  - mdata is stripped by default;
  - `nondep` is normalised to false;
  - fvars and mvars panic;
  - a nat literal pulls in the `Nat` dependency; a string literal pulls in `Char.ofNat` and `String.ofList`;
  - unsafe and partial declarations are omitted unless `--export-unsafe` (commit 0c79a8b2a, 2026-08-25).
- **Recomputation**: the redundant recursor, constructor and info fields **must be recomputed and compared, not trusted**. leanchecker `--from-export` drops the exported Quot.mk/lift/ind entries and checks afterwards that the regenerated ones match [P] (`L/src/LeanChecker.lean`).
- **Mathlib export size** (ARENA, lean 4.36.0, Mathlib fc4f59e577fe): **6,326,141,213 bytes (5.9 GiB), 112,081,718 lines** [P]. In ROUND (lean 4.29.1) it was 5.2 GiB and 100.0 M lines [P].

### 4.2 leanchecker [P] (`L/src/LeanChecker.lean`, 159 lines)

Modes:
- **default**: replay each module's new constants on top of its imports, in parallel IO tasks;
- `--fresh <mod>`: replay one module into an empty environment;
- `--from-export f.ndjson`: parse and replay into a fresh kernel environment, single-threaded as run by the arena.

It reads the `.olean`, `.server` and `.private` parts. `leanchecker-paranoid` is the same, statically linked against mimalloc in secure mode (level 3).

### 4.3 `lake check` and `lake comparator` [P] (`L/src/lake/Lake/CLI/Check.lean`, 1076 lines)

- **Sandbox**: the build and export run in a bwrap sandbox. Only the NDJSON export crosses the boundary; no olean is mapped into the judging process.
- **Run order**: the configured `external_kernels`, then the bundled ones (`--paranoid`), then the builtin kernel last: `leanchecker --silent --from-export`.
- **Bundled checker pins** (`L/src/CMakeLists.txt`):
  - lean4lean: Kha/lean4lean, tag lean4-bundle-4.35, `--import`;
  - nanoda_lib: 8de7e0c4ed30, `num_threads 4`;
  - con-leche: 6810492c1ccc;
  - con-ron: 42a086407cab (built with cargo).
- **Comparator semantics**:
  - `compareAt` checks that challenge and solution agree on the theorem targets, the legal axioms, `primitiveTargets` (1.7) and `Quot.*` if `Quot.sound` is permitted;
  - `checkAxioms` restricts axioms to the permitted list.
- **Standalone comparator** (https://github.com/leanprover/comparator):
  - the README says it is **deprecated**: "merged into core as of Lean release v4.35.0 in the form of `lake comparator`" [P];
  - comparator#68 (constants reached only through `Expr.proj` were not compared) was closed 2026-08-10 as completed, fixed via lean4#14728 [P] (https://github.com/leanprover/comparator/issues/68);
  - comparator#85 (substitution of a definition's value) was **withdrawn by its reporter**, who wrote that it existed "in a local fork's patches, not in upstream" [P] (https://github.com/leanprover/comparator/issues/85);
  - RFC lean4#15800 (conditional matches, exit 3) was **closed not_planned** on 2026-10-24; Kha: "this is effectively all covered by axioms" [P].

### 4.4 The .olean format [P] (`L/src/library/module.cpp` lines 106–145)

- **Header** (88 bytes on 64-bit, packed):
  - `"olean"` (5 bytes);
  - `OLEAN_VERSION` = **4** (1 byte);
  - flags (bit 0 = GMP bignum encoding);
  - `lean_version[33]`;
  - `githash[40]`;
  - `base_addr` (size_t).
- **After the header**:
  - `data_size`;
  - the compacted object graph;
  - `u32` closure-offset count and offsets;
  - a `u32` lib-relocation table.
- **Load**: the file is mmapped at `base_addr` (`MAP_PRIVATE`, writable) if possible; otherwise it is read and relocated. Loading **requires exactly the same githash**, version and flags.
- Implication: oleans are a version-locked, pointer-relocatable heap image of Lean runtime objects. A Rust kernel should take NDJSON (or a binary equivalent) as input and not parse oleans, unless it reimplements the compactor layout for exactly one githash [U, design inference].

---

## 5. Kernel Arena

### 5.1 What the arena is [P] (https://arena.lean-lang.org/, ARENA, https://github.com/leanprover/lean-kernel-arena)

- Each checker runs `$IN` on NDJSON exports. Outcomes are accept (exit 0), reject (exit 1) and decline (exit 2).
- **Time** is virtual: instructions ÷ 6.0 Ginstr/s, so it ignores parallelism. Wall time and max RSS are also recorded.
- Mathlib is `skip-on-ci`, with a 5680 s timeout.
- **Tests now (ARENA)**: 265 tests, of which 145 accept, 90 reject and 30 either.

  | Group | Tests |
  |---|---|
  | tutorial | 94 accept / 47 reject |
  | bugs | 30 reject |
  | corner-cases | 30 either + 1 accept |
  | perf | 36 accept / 8 reject |
  | other | 5 / 5 |
  | Libraries (cedar, con-leche, cslib, init, init-prelude, mathlib, navier-stokes-euler, reachability, std) | 1 accept each |

  The downloadable tarball omits tests over 10 MB, which is why it shows 135 accept and 90 reject.
- **Test metadata** (ARENA): `lean_version` of the test exports is 4.36.0 for 240 tests; 4.29.1 for 16; 4.34.x for 6 (including navier-stokes, 4.34.0-rc2); 4.35.0 for 3.
- **Round 2026-09 (ROUND)**:
  - Zenodo DOI 10.5281/zenodo.22944094, published 2026-09-24, "Lean Kernel Arena, Round 2026-09", editor Joachim Breitner;
  - 219 tests (130 accept / 71 reject / 18 either), **26 checkers**;
  - files: results.json 4.2 MB, site 4.0 MB, tests 3.5 MB;
  - "Results are only comparable within a round" [P] (https://zenodo.org/records/22944094, https://arena.lean-lang.org/round/).

### 5.2 Mathlib results: live ARENA (2026-11-21) [P]

Columns are virtual Ginstr, virtual minutes, wall seconds and max RSS in GiB. Correctness counts are over the 235 accept/reject tests ("err" means a timeout or crash).

| Checker | Lang | Version | Thr | Ginstr | Virt min | Wall s | RSS GiB | Correct / incorrect / decl / err |
|---|---|---|---:|---:|---:|---:|---:|---|
| nano-lean | Rust | v0.4.2 5cd4a25 | 4 | 395 | 1.1 | 50 | 5.0 | 235 / 0 / 2 / 0 |
| gruszka (NbE, Susz binary input) | Rust | a1a3864 | 4 | 513 | 1.4 | 32 | 2.4 | 235 / 0 / 0 / 0 |
| sokonanoda | Rust | 9a021b6 | – | 528 | 1.5 | 54 | 5.0 | 232 / 0 / 2 / 3 |
| mathgraph | Rust | flash | – | 912 | 2.5 | 179 | 6.2 | 227 / **8** / 0 / 2 |
| pestka | Aver | 1b6b06c | 4 | 1702 | 4.7 | 148 | 3.4 | 235 / 0 / 0 / 0 |
| kefir | Rust | 095cff9 | 1 | 2582 | 7.2 | 430 | 2.5 | 235 / 0 / 0 / 0 |
| palladium | Rust | f9d85c0 | 4 | 2831 | 7.9 | 162 | 3.9 | 229 / 0 / 0 / 6 |
| nanoclo | Rust | b8cefd0 | – | 3011 | 8.4 | 256 | 7.4 | 233 / **2** / 0 / 0 |
| con-ron (verified via Aeneas) | Rust | de06320 | 4 | 3474 | 9.7 | 178 | 4.4 | 226 / 0 / 9 / 0 |
| con-agua | x86-64 asm | fa516c1 | 4 | 3926 | 10.9 | 167 | 11.6 | 226 / 0 / 9 / 0 |
| nanobruijn | Rust | 2712fa6 | – | 4707 | 13.1 | 405 | 6.8 | 235 / 0 / 0 / 2 |
| nanoda | Rust | 0da9f98 | – | 5775 | 16.0 | 442 | 6.0 | 233 / 0 / 2 / 2 |
| con-leche (verified, `--verified --jobs=4`) | Lean | 600d3b5 | 4 | 6135 | 17.0 | 206 | 4.8 | 226 / 0 / 9 / 0 |
| tenet-jvm | Java | 0.1.5 | – | 9431 | 26.2 | 1255 | 12.1 | 235 / 0 / 0 / 2 |
| official-nightly | C++ | nightly-2026-11-14 | 1 | 9816 | 27.3 | 2575 | 9.9 | 235 / 0 / 0 / 0 |
| eink0rn | Haskell | 1.1.6 | 8 | 10614 | 29.5 | 362 | 13.5 | 232 / 0 / 3 / 2 |
| **official** | C++ | **v4.35.0** | 1 | **12095** | **33.6** | **2696** | **9.9** | 235 / 0 / 0 / 2 (corner-case timeouts) |
| ind-models | Lean | 86caadd | – | 12941 | 35.9 | 1586 | 6.0 | 235 / 0 / 0 / 2 |
| tenet | C# | 0.11.4 | 4 | 16986 | 47.2 | 546 | 11.6 | 235 / 0 / 0 / 0 |
| tenet-hs | Haskell | 0.1.4 | – | 19270 | 53.5 | 2621 | 11.6 | 234 / 0 / 0 / 1 |

Checkers that **did not pass Mathlib** in ARENA [P]:
- lean4lean (bce3448): rejected, "unknown constant 'instDecidableEqBool'", 22 incorrect. This is fallout from the new `Decidable` structure in the 4.36.0 exports.
- metalean-fast and canonical-min: rejected.
- kiota, ocaml4lean and nanoclo-fortran: errors.
- lazylean: timed out (3 incorrect).
- evmlean (Solidity), lean4cobol (COBOL, 18 incorrect), mini, rpylean (Python), logos-kernel and metalean-slow: declined.
- overfull (TeX) and vow-lean-kernel: timed out.

In total there are 37 checkers; the language field has 13 distinct values.

**The official kernel on the other large tests** (v4.35.0, virtual s / GiB) [P] ARENA:

| Test | Virtual s | GiB |
|---|---:|---:|
| init | 66.9 | 0.58 |
| std | 111 | 0.91 |
| cedar | 147 | 1.4 |
| con-leche | 216 | 7.0 |
| cslib | 566 | 3.5 |
| navier-stokes-euler | 672 | 2.5 |
| reachability | 23.5 | 1.6 |

### 5.3 ROUND 2026-09 Mathlib results (lean 4.29.1 export, 5.2 GiB) [P] ROUND

| Checker | Version | Virt min | GiB | Note |
|---|---|---:|---:|---|
| mathgraph | flash | 2.0 | 5.6 | |
| sokonanoda | 28c03d0 | 2.1 | 5.9 | |
| **parse-only** | v4.34.0 | **4.6** | 7.6 | Lean's NDJSON parser alone: 1664 Ginstr |
| nanoclo | 62671ff | 8.5 | 5.8 | |
| con-ron | 39de395 | 9.8 | 6.6 | 13 declined |
| lazylean | 0.3.0 | 15.4 | 5.6 | |
| still-nanoda | 06a07b7 | 15.5 | 5.2 | 8 incorrect |
| nanoda | 4c544ed | 18.0 | 7.4 | |
| nanobruijn | 3a86285 | 21.0 | 6.1 | |
| con-leche | 78ded4b | 22.3 | 8.0 | |
| eink0rn | 1.1.6 | 27.0 | 12.0 | |
| ind-models | 4130f57 | 31.6 | 8.0 | |
| **official** | **v4.34.0** | **32.9** | 7.6 | 11832 Ginstr, wall 3302 s |
| lean4lean | bce3448 | 39.9 | 9.3 | |
| official-v4.28.0 | 4.28.0 | 41.4 | 9.4 | **6 incorrect**: accepted bad bug tests later fixed |
| tenet | 0.11.1 | 45.9 | 12.8 | |
| nanoclo-fortran | b3a13ef | 50.4 | 13.5 | |

### 5.4 What this means for "10x faster than official" [P numbers; U interpretation]

- **Baseline**: official v4.35.0 is 12,095 Ginstr, 33.6 virtual minutes and 44.9 min wall, single-threaded, at 9.9 GiB. Nightly-2026-11-14 is 9,816 Ginstr (27.3 min); the gain came from the Oct–Nov perf PRs.
- **10x target**: 10x on v4.35.0 is about 1,210 Ginstr, or **about 3.4 virtual minutes**.
- **Already beaten**: four Rust checkers are already 13–31x fewer instructions: nano-lean 30.6x, gruszka 23.6x, sokonanoda 22.9x, mathgraph 13.3x (but mathgraph has 8 incorrect results). On wall time, nano-lean takes 50 s on 4 threads against 2696 s, 54x.
- **Parsing cost**: parsing the NDJSON alone costs Lean about 1.66 T instructions (ROUND parse-only), about 14% of the official total. A 10x kernel needs a parser much faster than that; gruszka avoids the problem by using a binary format (Susz).
- **Accepted sets differ**: those fast checkers do not match the official kernel on all 30 corner cases. "Exactly the official accepted set" is a stronger requirement than the arena measures. The arena's "either" category is precisely where rulean must copy official behaviour for the pinned version.
- **Test outcomes are pinned to the lean version of each export**: the bug tests are all "reject", matching v4.35.0 or later.

---

## 6. Mathlib size and the kernel's share of build time

| Metric | Value | Tag and source |
|---|---|---|
| Theorems / definitions / contributors | **296,300 / 142,131 / 772** (no date on the page; fetched 2026-11-21) | [P] https://mathlib.org/mathlib_stats.html (the old URL leanprover-community.github.io/mathlib_stats.html now redirects there) |
| Old notes, 2026-10-25 | 291,178 / 139,569 / 772 | Plausible, about 1 month earlier [U] |
| Files and lines | 9,437 files, 2,481,682 lines (old notes, gitstats4.js) | [U] not re-fetched; the new page shows no numbers |
| Export | 5.9 GiB, 112.1 M NDJSON lines (Mathlib fc4f59e577fe, Lean 4.36.0) | [P] ARENA |
| Official full-Mathlib kernel replay | 33.6 virtual min, 44.9 min wall single-thread (`--from-export`) | [P] ARENA |
| Third-party claim | "around fifteen minutes" for the official kernel to replay Mathlib (presumably the parallel default mode); elaboration dominates a cold build of "CPU-hours" | [S] https://www.stephendiehl.com/posts/dependently_typed_future/ |
| Kernel share of a Mathlib build | **No published measurement found.** Rough estimate: about 45 CPU-min of kernel against several CPU-hours of build gives a single-digit to low-double-digit % share | [U] |
| Hot spots where the kernel dominates | `ring` closed exponents: 36.28 s against 3.07 s with `debug.skipKernelTC` | [S] https://github.com/leanprover-community/mathlib4/issues/44873 |
| | `lia` literal-linear kernel time | [S] lean4#16311 |
| | vcgen: 246 s → 0.53 s kernel | [P] RN(4.35.0) |
| | PlanarPacking: 9–11 h official against 11 min nanoda on 64 threads | [S] https://github.com/nealmcb/openai-math-lean-tooling |

Implication [U]: most of the user-visible benefit of a 10x kernel comes from (a) `lake check` / `--paranoid` re-checks, which are pure kernel time and are now the recommended workflow (the roadmap wants `lake build` to skip the kernel), and (b) pathological single declarations. It does not come from ordinary `lake build`.

---

## 7. Exact semantics checklist

Target: **pin one official version.** Proposal: v4.36.0, the current stable, whose kernel is identical in semantics to v4.35.0. Track v4.37 as a flag set.
Every item below is [P] from `L/src/kernel/*` or the tag file named, unless marked. Version-dependent items are labelled ⟨≤4.36⟩, ⟨4.37⟩ or ⟨master⟩.

**Input and environment**
- [ ] Parse NDJSON 3.1.0 exactly (4.1).
  - Name/level index 0 is implicit.
  - `natVal` is decimal and unbounded, but literals larger than LEAN_NAT_MAX_SIZE (128 MiB) must reject.
  - `strVal` is a Lean String: UTF-8, with chars as Unicode scalars.
- [ ] Ignore exported recursors, constructor info and Quot types for *trust*. Regenerate them and compare with the exported data, as leanchecker does for Quot.
- [ ] Reject a duplicate declaration name, duplicate level params, undeclared level params in any expr, and loose bvars in any declaration or inductive (#16512).
- [ ] Treat `Nat`, `Nat.zero/succ/add/…/shiftRight`, `Bool.true/false`, `String`, `String.ofList`, `Char.ofNat`, `List`, `eagerReduce` and `Eq` (for Quot) as built-in by **name**, as the official kernel does (no definitional check). Optionally also offer a strict mode that verifies them.
- [ ] Safety:
  - unsafe constants cannot be referenced from safe or partial declarations;
  - partial constants cannot be referenced from safe ones;
  - the lean4export default omits unsafe and partial declarations entirely.

**Universes**
- [ ] `mk_max`/`mk_imax` simplifications exactly as in 1.10, including `imax 1 u = u` (#7631).
- [ ] `is_equivalent` = structural or `normalize` equality. **Do not use a complete decision procedure**: corner cases imax-nested-absorption and imax-right-successor must reject.
- [ ] `is_geq` uses the official algorithm. `normalizes_to_zero` is used for Prop detection.

**Typing**
- [ ] `infer_proj`: the struct type's head is `proj_sname`, has 1 constructor, `nargs == nparams + nindices`, and idx < nfields. Apply the Prop-projection restriction (1.9), including `imax`-Prop.
- [ ] `is_prop` fails closed on stuck sorts (#14807).
- [ ] let: the value type must be defeq to the declared type. Check binders before extending the context.
- [ ] Theorems: the type must be a Prop; the value type must be defeq.
- [ ] Definitions (safe): checked without themselves in scope. Mutual definitions: only unsafe or partial, same lparams, same safety.

**Reduction and def-eq**
- [ ] `whnf_core`:
  - beta, zeta (let and let-fvar);
  - proj with the constructor-inductive == sname check;
  - recursor iota with K, structure eta, and nat and string literal conversion;
  - Quot.lift and Quot.ind on Quot.mk.
- [ ] Major premise handling:
  - ⟨≤4.36⟩: always `whnf` the major.
  - ⟨4.37⟩: skip whnf when the major's type is a Prop, and eta-expand subsingleton structure majors (#15371).
- [ ] Delta:
  - unfold definitions **and theorems** (`constant_info::has_value`);
  - never opaque, axiom, quot, inductive, constructor or recursor constants;
  - use the hint order Abbrev, then Regular by height, then Opaque/theorem.
- [ ] Nat extension: exactly the 15 ops of 1.7.
  - Arguments are reduced with full `whnf`.
  - `Nat.zero` counts as a literal.
  - Size guards on succ, add, sub, mul, pow and shiftLeft; the exponent or shift must be ≤ UINT_MAX, otherwise an error (reject).
  - In lazy delta, only on fvar-free terms unless `eagerReduce` is set.
- [ ] Bool.true shortcut. String-literal expansion against `String.ofList`.
- [ ] Def-eq order exactly as in 1.8, including the position of proof irrelevance: ⟨≤4.36⟩ after `whnf_core`; ⟨4.37⟩ before it.
- [ ] Def-eq is **not transitive**. Cache successes only, keyed on ordered pairs; never union-find (#14806).
- [ ] Eta:
  - function eta;
  - struct eta for non-recursive one-constructor zero-index inductives (types must be defeq);
  - ⟨4.37⟩ partial-constructor eta (#15373);
  - unit-like only for **0-field** non-recursive structures. #15372 was reverted, so do not extend it.
- [ ] `is_def_eq_offset` handles `succ` against a literal against `Nat.zero`. `lazy_delta_proj_reduction` handles proj against proj.

**Inductives**
- [ ] `check_uniform_ind_occs` (#14582).
- [ ] All types share params and the result universe (with `is_equivalent`).
- [ ] Strict positivity (skipped for unsafe).
- [ ] Field universe ≤ result, or the result is Prop.
- [ ] Indices do not mention the types being declared.
- [ ] Nested inductives: auxiliary translation, type-checking the Ds (#14577), reserving the `_nested` prefix, and re-checking the restored result.
- [ ] Large-elimination rule exactly as in 1.11. ⟨master⟩ adds "recursive Prop → small only" (#13851).
- [ ] K flag only for a 1-constructor, 0-field, non-mutual Prop type.
- [ ] Generated recursor types and rules equal the official ones up to α-equivalence, *and* they type-check (#14808).
- [ ] Counts are 64-bit; reject numParams ≥ 2^32 rather than truncating (#16279).

**Quot**
- [ ] Requires the exact `Eq` shape. The four names must be fresh. Hard-coded types; iota as in 1.6.

**Resources** (these affect acceptance only through timeouts)
- [ ] Official limits: recursion 16 × maxRecDepth; heartbeats per declaration; the 128 MiB numeral bound.
- [ ] The arena gives 60 s per corner case; v4.35.0 times out on the 2 eta-struct-major-*-no-whnf cases.
- [ ] Define rulean's limits as "at least official", and document deliberate divergences: accepting where the official kernel times out [U policy].

**Validation corpus**
- [ ] All 235 decidable ARENA tests.
- [ ] The 30 corner cases must match the pinned official version's outcome, not merely be "either".
- [ ] Mathlib, cslib, std and init exports for the pinned version.
- [ ] The official test suite `tests/lean/run/*kernel*` and the soundness regression tests in each bug-hunt PR. #13851 *removed* 4 regression tests, so take them from v4.36.0.

---

## 8. Formal-verification landscape (relevant to "formally verified")

| Artifact | What is proved | Language | Mathlib (ARENA) | Source |
|---|---|---|---|---|
| con-leche | Accepted environment ⇒ a set-theoretic model exists (consistency); the proof is checked by the official kernel; assumes ZFC with inaccessibles. Declines non-standard axioms. Written by Claude under Breitner | Lean | 17.0 min virtual, 206 s wall at 4 threads (VK: about 100 s at 8 threads) | [P] VK, ARENA |
| con-ron | Rust refines a Lean twin, which refines con-leche (Aeneas) | Rust | 9.7 min, 178 s wall | [P] ARENA checker description |
| ind-models | Inductive types have models | Lean | 35.9 min | [P] ARENA |
| lean4lean | Metatheory in progress; a port of the C++ code | Lean | currently failing on 4.36 exports; 39.9 min in ROUND | [P] ARENA, ROUND; arXiv:2403.14064 |

- Hales: "no complete, public relative-consistency proof covering Lean abstract type theory" [S].
- The verified checkers decline 9 definite tests (ARENA). So "verified" and "accepts exactly the official set" are in tension today. Rulean's spec must say whether the proof covers soundness only (accept ⇒ model) or also completeness relative to the official kernel [U].

---

## 9. Audit of the old notes, `Spec/2148/01-research-2026.md` §1.2

| Old claim | Verdict | Correction and source |
|---|---|---|
| Latest stable v4.35.0, RC v4.36.0-rc1 | **Outdated** | v4.36.0 is stable (2026-11-16); v4.37.0-rc1 is out (2026-11-18) [P] GitHub releases |
| 4.31 on Jun 13 | Minor | GitHub publish date is 06-15 [P] |
| v4.35.0: lake check, paranoid, Linux-only sandbox, Decidable a structure, reduceBool etc. removed, native_decide axiom | **Correct** | [P] RN(4.35.0). Add: `leanchecker --from-export`, runtime-soundness fixes #15241, #15288, #15289 |
| Arena "127 good / 72 bad + Mathlib" | **Wrong** for both dates | ROUND: 219 tests = 130/71/18. Now: 265 = 145/90/30 [P] |
| "About 25 kernels" | [S] Hales | ROUND has 26 checkers, ARENA 37 [P] |
| nanoda: under 5,000 LOC, 15.6 min, 6 GB | LOC [P] WW; **timing not reproducible** | ROUND: 18.0 min / 7.4 GiB; ARENA: 16.0 min / 6.0 GiB [P] |
| lean4lean 38.8 min / 11.6 GB | **Not matching** | ROUND: 39.9 min / 9.3 GiB; ARENA: fails Mathlib (instDecidableEqBool) [P] |
| con-leche about 100 s on 8 threads | **Correct as a VK quote** | ARENA (4 threads): 206 s wall, 17.0 virtual min, 4.8 GiB [P] |
| con-ron refines via Aeneas; ind-models checks inductive models | Correct | [P] |
| #14576: "all versions up to v4.31.0" | **Imprecise** | That is the CVE wording, but v4.32.0 and v4.32.1 predate the fix; first fixed release v4.32.2, 07-28 [P/U] |
| "Fix within about an hour" | Roughly correct | PR opened about 1.7 h after the report; merged 07-29 [P] |
| Week-old nanoda accepted it via a separate bug | Correct | Proj type-name check [P] PM1 |
| Bug hunt Jul 30–Aug 20; v4.33.1; GMP 6.3.0 | Correct | Add #14582, #14808, #14849 and the later #15241/#15288/#15289 in v4.35.0 [P] |
| March 2026: Opus 4.6, 7 Rocq bugs, 2 nanoda bugs | Correct | [P] WW |
| "AIs are really good at exploiting…" quote | Unverified | Not found in the posts I read [U] |
| Hales guest post 2026-10-09 | Correct | [S] |
| Trust stack | Mostly correct | Comparator is now `lake comparator` in core; the standalone repo is deprecated [P] |
| comparator #68 / #85 open, fix status [U] | **Resolved** | #68 fixed (lean4#14728); #85 was a **false report**, withdrawn [P] |
| RFC #15800 conditional matches | **Closed, not planned** (10-24) | [P] |
| Mathlib 291,178 thm / 139,569 def / 772 (10-25) | Superseded | 296,300 / 142,131 / 772 at mathlib.org [P]. The 9,437 files / 2.48 M lines figure was not re-verified [U] |
| openwall link | Correct | Plus the CVE follow-up, CVE-2026-72844 [P] |
| (missing) theorems still unfolded by the kernel | **New** | 1.3 |
| (missing) version drift: #15103, #15371, #15373 in 4.37; #13851 on master | **New** | 1.15 |

## 10. Open questions [U]

1. The exact mechanism by which the #14576 PoC's hash collision "defeats kernel caching". It may involve the expr_eq_fn cache or equiv_manager hashing. Read #14577 and `expr_eq_fn.cpp` before designing rulean's caches.
2. Whether `infer_only` is used for theorem values in `add_theorem`. This affects only performance, not acceptance, provided the full check runs.
3. A measured kernel share of Mathlib build time (look at radar.lean-lang.org and Zulip `debug.skipKernelTC`).
4. LOC for the arena kernels: the arena does not publish it. Count from the repos if needed.
5. The 2022 bignum bug: identify its PR, and whether the kernel or the runtime was at fault.
