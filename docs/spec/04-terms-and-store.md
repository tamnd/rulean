# 04. Terms and the store

This document specifies how rulean represents names, levels, expressions, values, local contexts and big numbers in memory. The representation is the second-largest source of speed after the evaluation strategy. con-ron is 2.3x cheaper than con-leche with the same algorithm, and representation is the only difference (B§8.1). The representation must also fit the Aeneas subset (10.6).

## 04.1 Principles

1. **Handles, not pointers.** Every object is a `u32` handle into a typed table. There is no reference counting and no garbage collector. Memory is freed by tier (04.8).
2. **Hash-consing.** Each table interns its objects. Two structurally equal objects in one tier have the same handle. Equal handles mean equal terms. Unequal handles in the same tier mean unequal terms.
3. **Struct of arrays, one array per constructor.** Applications are about 85% of expression nodes (B§8.1). An application node is two `u32` handles, 8 bytes.
4. **Cached data is computed, never read.** The hash, the loose bound variable range and the flags of a node are computed when the node is made. Input files never supply them (07.3.3).
5. **Deterministic.** Handle values depend only on the order of insertion. Hashes use a fixed function with no random seed. Two runs on the same input build the same store.

## 04.2 Expressions

### 04.2.1 Handle

```
ExprId = u32
  bit 31      : tier (0 = frozen, 1 = scratch)
  bits 27..30 : kind (bvar, sort, const, app, lam, pi, let, lit, proj, fvar)   -- 4 bits
  bits 0..26  : index into the array of that kind in that tier                 -- 2^27 = 134 M per kind per tier
```

- The kind is in the handle, so a `match` on the kind needs no memory load.
- 134 M entries per kind and tier is enough: Mathlib's export has 112 M lines in total for all record kinds (A§4.1). FLT (Anthropic) has a 37.8 GB export, about 6.4 times Mathlib. If a corpus needs more than 2^27 nodes of one kind, the store switches to a 64-bit handle build (`--features wide`). That build is a separate type, checked by the same proof with a generic width.
- In the `wide` build, `ExprId` holds a `u64`: bit 63 is the tier, bits 59..62 are the kind and bits 0..58 are the index. The type `Raw` of `rulean-store` is the integer type of the handle, `u32` or `u64`. The memo tables, the session table and the index tables of the parsers store values of type `Raw`. A hash mixes the low 32 bits and then the high 32 bits of a `Raw` value, so the hashes of the two builds are different. `NameId`, `LevelId` and the other handles stay 32 bits in both builds.
- `rulean version` gives the width of the build. On Init of v4.36.0, `rulean olean` in the `wide` build uses 3.5% more instructions and 27% more memory than in the default build, and it gives the same verdict. CI runs clippy and the tests on the `wide` build. The `.rlb` format keeps 32-bit expression indices, so a file has at most 2^32 expressions in both builds.

### 04.2.2 Node arrays

| Kind | Fields | Bytes per node |
|---|---|---|
| bvar | index u32 | 4 |
| sort | level LevelId | 4 |
| const | name NameId, levels LevelListId | 8 |
| app | fn ExprId, arg ExprId | 8 |
| lam, pi | binder name NameId, binder info u8, domain ExprId, body ExprId | 13, stored as 16 |
| let | name NameId, type ExprId, value ExprId, body ExprId | 16 |
| lit | NatId or StrId with a tag bit | 4 |
| proj | struct name NameId, index u32, struct ExprId | 12 |
| fvar | de Bruijn level u32, type ExprId (only in scratch) | 8 |

Each node also has a **side record** of 8 bytes in a parallel array:

```
hash            : u32     (rulean's own hash function, 04.2.3)
loose_bvar_max  : u24     (the loose bound variable range; saturates; a saturated node is never cached by range)
flags           : u8      (has_fvar, has_level_param, has_let, has_proj, has_lit, is_closed_prop_hint, …)
```

`mdata` nodes are never stored. The parser strips them (07.1.2).

### 04.2.3 Hash function

- The hash is a 32-bit mix of the kind seed and the hashes of the children, with a MurmurHash3-style step. Lean moved to a similar step in v4.37 for the same reason (D§3.4, PR#16107).
- Literal hashes cover all bits of the number (lean4#16146), so literals that differ only above 2^64 do not collide.
- The hash of a large literal has four lanes of 64 bits. Each limb goes into the lane of its position modulo 4 with one multiplication and one rotation, and at the end the MurmurHash3 step mixes the halves of the lanes and the limb count. The four lanes do not depend on each other, so the processor runs them at the same time. The MurmurHash3 step for each limb has a chain of six multiplications, and on `perf/gf3-matrix-product`, with values of up to 19,000 limbs, the hash took more time than the operations.
- Hash collisions are never a soundness problem: a table lookup compares the full node after the hash matches. Collisions cost time only. The #14576 exploit used a hash collision to defeat caching (A§2.1), so rulean's caches never trust a hash alone (08.5).

### 04.2.4 Interning tables

- Each kind has an open-addressing table from `(hash, fields)` to index. It is the verified `rulean_store::Table` (10.6), not `std::collections`.
- A slot of the table is one record with the 32-bit hash and the handle, and in a table with epochs also the epoch. So one step of a walk reads one cache line. The memo maps of the checker keep the two keys and the value of an entry in one record for the same reason. On the Init export of v4.36.0, this layout takes 4% of the instructions and 10% of the peak memory off `rulean check`, against one array for each field.
- The frozen tier's tables are read-only after `freeze`. Workers look up in the frozen table first, then in their own scratch table.
- A scratch node whose fields are all frozen and that already exists in the frozen tier gets the frozen handle. So a term has one handle no matter which worker made it. This keeps cache keys equal across workers.

## 04.3 Names and levels

- **Names** are interned in a table with two kinds (`str`, `num`) and a prefix handle. Strings are interned in a string table. `NameId 0` is the anonymous name, as in the export (07.1).
- **Levels** are interned with kinds `zero`, `succ`, `max`, `imax`, `param`. `LevelId 0` is zero.
- **Level lists** for `const` nodes are interned as their own table, so a `const` node is 8 bytes.
- **Level caches.** `normalize(l)` and `instantiate_lparams(l, us)` are cached per handle for the whole run. Levels are a tiny part of memory.

## 04.4 Local contexts

- A local context is a stack of entries `(name, type, value?)`. A free variable is its de Bruijn level in this stack.
- Free variable nodes (`fvar`) are created only in scratch. They carry the level and the type handle. Two free variables with the same level and the same type in the same declaration are the same node.
- Because free variables are named by level, entering a binder never renames existing terms. Cache keys that mention free variables stay valid inside deeper binders (B§8.1).

## 04.5 Values (engine F)

Values for NbE (05.4) live in a per-worker **value arena**:

- Value nodes, closures, environments and spines are in typed `Vec`s indexed by `u32`. Closures are records `(EnvId, ExprId)`. There are no Rust closures (10.6).
- Environments are persistent lists: `EnvId → (ValueId, parent EnvId)`.
- Spines are chunked arrays, so `apply` to a neutral value appends without copying.
- Glued values store the folded constant application and an `Option<ValueId>` slot for the unfolding. The slot is filled once (call by need).
- The arena is cleared at the end of each declaration by resetting the vector lengths. Values never cross declarations. Session caches (08.4) store terms, not values.

## 04.6 Natural numbers

`rulean_nat::Nat` is rulean's own bignum. No C library is used (13.3), and the official kernel's dependence on GMP was a soundness risk in 2026 (#14833, A§2.2).

```
enum Nat { Small(u64), Large(Limbs) }   -- Large is canonical: at least 2 limbs or a value ≥ 2^64; no leading zero limb
```

- The 15 kernel operations (05.8) each have a fast path for `Small` with overflow checks.
- `Large` uses schoolbook multiplication when an operand has fewer than 48 limbs, Karatsuba above. The Karatsuba step uses the subtractive form and writes the result in place, and an operand that is much longer than the other is cut into parts. The schoolbook loop does four rows in one pass on the long operand (perf/10.9). Division uses Knuth algorithm D. No FFT. Results above 128 MiB are refused by the caller before the operation runs (05.8). The schoolbook loop has the shorter operand in the outer loop, so the inner loop is long. The addition, the subtraction and the bitwise operations have one loop on the limbs of both operands and one loop on the other limbs of the longer operand, with no test of the length in the loops.
- Each operation has a refinement proof against Lean's `Nat` (10.4.6). The differential test oracles are `num-bigint` and `malachite` (malachite is LGPL and is used only in tests, D§12.5).
- Literals are interned in a `NatId` table, so equal literals have equal handles.

**Performance note.** Mathlib literals are almost all below 2^64 (B§8.6). The `Large` path matters for `decide`-heavy proofs and for the Arena literal tests. Its target is at most 3 times the time of `num-bigint` on the operations and sizes of the Arena literal tests.

## 04.7 The declaration stream

All input formats (07) decode to one Rust type:

```
Decl ::= Axiom   { name, lparams, type, safety }
       | Defn    { name, lparams, type, value, hints, safety, all }
       | Thm     { name, lparams, type, value, all }
       | Opaque  { name, lparams, type, value, safety, all }
       | Quot    { name, lparams, type, kind }
       | Induct  { lparams, nparams, types: [(name, type)], ctors: [[(name, type)]], safety, exported_recs }
       | Mutual  [Defn]
```

Handles in a `Decl` refer to the frozen tier. `Mutual` is a block of unsafe or partial definitions that can refer to each other, as the `mutualDefnDecl` declaration of Lean. The checker adds it with the rules of a mutual definition (05). NDJSON has no form for it, and the `.olean` reader gives it (07.3.4). The Lean twin has the same type. `Spec.parseStream` (10.5) returns a list of the Lean version of `Decl`.

## 04.8 Tiers and lifetimes

| Tier | Holds | Written by | Lifetime |
|---|---|---|---|
| frozen | all input terms, names, levels, literals; the constants of the environment | the parser, single-threaded or merged in parallel (07.1.3) | the whole run |
| scratch, per worker | terms made during checking (instantiations, inferred types, free variables) | one worker | one declaration, cleared by an epoch counter |
| value arena, per worker | NbE values | one worker | one declaration |
| session cache, per worker | cached judgments on frozen terms (08.4) | one worker | the whole run |
| promoted | scratch terms that a session cache entry keeps | one worker, moved to a worker-private persistent tier | the whole run |

- **Epoch clearing.** The scratch tables carry an epoch number in each slot. Clearing the scratch tier increments the epoch, so it is O(1). This is con-ron's `HashMap2` method (B§8.1).
- **Promotion.** A session cache entry may need an inferred type that lives in scratch. Before the scratch tier is cleared, such terms are copied into a worker-private persistent tier. The copy is bounded: at most 10% of the scratch size per declaration, or the entry is dropped (08.4).

## 04.9 Memory budget

| Item | Mathlib estimate | Basis |
|---|---|---|
| frozen expression nodes and side records | about 1.6 GiB | con-ron's store with 8-byte app nodes plus 8-byte side records (B§8.1); measured in M1 |
| names, levels, strings, literals | about 0.3 GiB | |
| constants table and dependency graph | about 0.2 GiB | about 700 k declarations |
| per-worker scratch, values and caches | about 0.2 GiB each, 8 workers | gruszka and con-ron per-worker data |
| **total target** | **at most 4 GiB** (P1.f) | con-ron 4.4 GiB, gruszka 2.4 GiB, official 9.9 GiB (A§5.2) |

The side records double the frozen node size. If M1 shows that the 4 GiB target is at risk, the side record moves to 4 bytes (hash only), and the range and flags are recomputed on demand with a cache.
