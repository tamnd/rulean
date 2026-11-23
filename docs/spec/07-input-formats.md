# 07. Input formats

rulean reads three formats:

- the lean4export NDJSON stream, which is the reference input;
- the rulean binary format, which is fast;
- the `.olean` module files, which are needed for checking without a separate export step.

All three decode to one declaration stream (04.7). The type checker never sees the file format.

Sources: research/A-lean-kernel.md section 4, research/D-runtime-formats-rust.md sections 3, 5, 6 and 7.

Parsing is a large part of the budget. The official parser alone takes about 1.66 T instructions on Mathlib, which is 14% of the official run (A§5.4). That is more than the whole P1.a budget of 1.21 T. So the parser target is strict (07.1.4).

## 07.1 lean4export NDJSON 3.x

### 07.1.1 Grammar

The format is version 3.1.0 (A§4.1). It has one JSON object on each line.

- **Line 1, meta:** `{"meta":{"exporter":{"name":…,"version":…},"lean":{"githash":…,"version":…},"format":{"version":"3.1.0"}}}`. rulean accepts major version 3, and any minor version up to the newest it knows. An unknown major version is a decline.
- **Names** (`"in"` index; index 0 is the anonymous name and is implicit): `{"str":{"pre":i,"str":s},"in":k}` and `{"num":{"pre":i,"i":n},"in":k}`.
- **Levels** (`"il"` index; index 0 is zero and is implicit): `succ`, `max`, `imax`, `param`.
- **Expressions** (`"ie"` index): `bvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE` (with `nondep`), `proj`, `natVal` (a decimal string), `strVal`, `mdata`.
- **Declarations:** `axiom`, `def`, `opaque`, `thm`, `quot`, `inductive`, with the fields of A§4.1.

### 07.1.2 Rules

- An index must be defined before it is used. A line that refers to an undefined index is a reject. Indices may have gaps and may be out of order (Arena tests `sparse-name-index` and `level-index-out-of-order`). The parser uses a growable table with a "defined" bit.
- An index that is defined twice is a reject.
- `natVal` is an unbounded decimal string. Leading zeros are allowed only for "0". A value above the literal bound (05.8) is a reject, and the parser checks this from the string length before any conversion.
- `strVal` must be valid UTF-8 with Unicode scalar values only. A JSON escape `\uD800` to `\uDFFF` without a pair is a reject.
- `mdata` is stripped. Its data is not parsed beyond JSON well-formedness.
- `nondep` is read but has no effect on checking. The exporter normalises it to false (A§4.1).
- Duplicate JSON keys, numbers with exponents or fractions where an integer is expected, and integers above 2^64 − 1 are rejects.
- A truncated last line is a reject. An empty line is a reject.
- Fields that rulean recomputes (06.1) are parsed and then compared, never trusted.

### 07.1.3 Scanner design

The scanner is hand-written for this grammar. It is not a general JSON library: the grammar is small and fixed, and a small scanner is easier to verify (D§9.5).

- The input is read in large blocks through `rulean-io` (10.7, K2), or mapped read-only with `memmap2`.
- Each line is dispatched on its first key. The scanner reads only the keys of that record kind, in any order.
- Numbers are parsed with a u64 fast path and an overflow check.
- Strings without escapes are borrowed from the input buffer and interned once. Strings with escapes are decoded into a scratch buffer.
- The scanner writes directly into the term store (04.2). It does not build an intermediate tree. Hash-consing happens at insertion.
- Optional SIMD line splitting is island K4 (10.7). The verified scalar scanner is the reference, and `--no-simd` turns the SIMD path off.

**Parallel parsing.** The first pass finds line boundaries and record kinds. Name, level and expression records form a dependency order by index, so they can be parsed in parallel by ranges into per-thread tables, then merged by index. Kontroli found that channel overhead cancelled the gain of parallel parsing (B§8.4). rulean parses ranges in place and merges tables, with no per-record messages. Parallel parsing is a performance option. It is outside the verified core (it uses island K1), and its output is compared with the scalar parser in CI.

### 07.1.4 Targets

| Measure | Target | Reference |
|---|---|---|
| instructions per input byte, scalar path | at most 25 | official parser about 300; nano-lean whole pipeline about 68 (B§10.2) |
| Mathlib parse, instructions | at most 0.16 T (13% of the P1.a budget) | official 1.66 T |
| Mathlib parse, wall time, 8 threads | at most 6 s | |
| peak memory during parse | at most the size of the final store plus 10% | |

## 07.2 The rulean binary format (`.rlb`)

### 07.2.1 Purpose

A binary format removes most of the parse cost. MM0 and gruszka show this (B§8.7, B§10.2). The FRO also asked for "binary export formats" (A§2.4, VK).

The binary format is a **cache, not a new source of truth**. It is made from an NDJSON export or from `.olean` files with `rulean pack` (09.2). The checker checks what it decodes. So a wrong encoder can cause a reject, but it cannot cause a wrong accept (10.5).

### 07.2.2 Layout

All integers are little-endian. All sections start at an 8-byte boundary. Version 1 has this layout.

```
header      : magic "RULEANB\0", format version u32 (1), flags u32 (0),
              lean version (32 bytes), lean githash (40 bytes),
              profile id u32 (0), section count u32, SHA-256 of the source export (32 bytes)
section dir : per section: kind u32, offset u64, length u64, item count u64, CRC-32C u32
sections    : STRINGS   (1: all lengths u32, then all UTF-8 bytes)
              NAMES     (2: tag u8, 3 zero bytes, prefix index u32, payload u64)
              LEVELS    (3: tag u8, 3 zero bytes, two operands u32)
              EXPRS     (4: one record of u32 words per node, children first)
              NATS      (5: limb count u32, a zero u32, then the u64 limbs)
              DECLS     (6: declaration records of u32 words with operand indices)
              DEPS      (7, optional: per-declaration dependency lists, for the scheduler, 08.3)
```

- The text fields of the header have zero bytes after the text. A version, a flag or a profile id that the decoder does not know is a decline. In version 1, the checker selects the profile from the Lean version (05.2).
- The name at index 0 is the anonymous name, and the level at index 0 is zero. The tables do not hold them. A payload of a string name is a string index. A payload of a number name is the number.
- The first word of an EXPRS record has the tag in its low byte: bvar, sort, const, app, lam, pi, let, nat literal, string literal, proj. For a binder, the second byte is the binder information. A const record has the name, the count of levels and the levels. The other operands are indices.
- The first word of a DECLS record is the tag: 1 axiom, 2 definition, 3 theorem, 4 opaque, 5 quotient, 6 inductive block, 7 mutual block. A mutual block has the count of definitions, then one definition record without the tag for each definition.
- A number has no zero top limb, so that each number has one form. The literal bound of 07.1.2 applies.
- The decoder reads the tables in this order: STRINGS, NAMES, LEVELS, NATS, EXPRS, DECLS. Every index refers to an item that the decoder already read, so decoding is one forward pass with bounds checks. An index to a later item is an undefined index.
- The decoder makes each node with the constructors of the store, so the store computes the hashes and the flags again. Hashes and flags are never read from the file. A later version can copy the EXPRS arrays directly into the frozen tier, if the decode cost is too high.
- A wrong checksum, a cut record, a nonzero pad, an unknown tag or a missing section is a reject of the input. A count must agree with the length of its section before the decoder allocates memory for it.
- The DEPS section is a hint. The scheduler recomputes dependencies when the hint is missing. A wrong hint can only cause a reject (unknown constant), never an accept. The version 1 encoder does not write it, and the version 1 decoder does not read it.

### 07.2.3 Targets and proof

- Decode at most 3 instructions per byte, so Mathlib decodes in at most 0.03 T.
- Decoder correctness is lemma 10.5: `Spec.parseBinary b = Spec.parseStream (ndjson_of b)`. The decoder is in the verified core. NDJSON has no form for a mutual block, so the lemma covers the files without tag 7.
- Other binary formats (Susz from gruszka, BLean from olean-export) are not read by rulean 1.0. A converter is a later option (15.3).

## 07.3 `.olean` files

### 07.3.1 Why rulean reads oleans

`lake check` runs an export step inside a sandbox before any external kernel runs (A§4.3). For Mathlib the export takes a long time: olean-export reports 1,526 s for lean4export against 18 s for its own reader (D§6). An olean reader lets rulean check a built project directly, and in in-process mode (09.6) the environment is loaded from oleans anyway.

### 07.3.2 The format

An `.olean` is a compacted heap image of Lean runtime objects (D§5, A§4.4).

- Header, 88 bytes: `"olean"`, version byte, flags (bit 0: GMP number encoding), `lean_version[33]`, `githash[40]`, `base_addr`.
- Version 2 (v4.33 to v4.36): data at offset 88, and the first word is the root pointer.
- Version 3 (v4.36, for `CompactedRegion.save` with closures): `data_size` at 88, data at 96, then the closure section (a `u32` count and the offsets) and the library table (a `u32` count and the entries). The first word of the data is the root pointer.
- Version 4 (v4.37.0-rc1, PR#16214): the layout of version 3 for all files, `[header][data_size][root][objects][closures][libs]`. Version 4 also marks the new `Expr` hash. In v4.37.0-rc1, `ModuleData` has two more fields, `constTrie?` and `extraConstTrie?`. These are prefix trees over the constant names, and the import of Lean finds the imported constants in `constTrie?`, not in `constants`.
- Objects have `m_rc = 0` and their size in `m_cs_sz`, so the region can be walked linearly.
- Pointers are absolute addresses that assume the region is mapped at `base_addr`.
- The module system writes three parts: `X.olean`, `X.olean.server`, `X.olean.private`. Later parts point into earlier parts. **In `X.olean`, theorems are stored as axioms (statement only).** A checker that reads only `X.olean` checks no proofs. rulean must read all three parts.

### 07.3.3 Reader rules

The official loader does no structural validation (I#16542). The rulean reader treats every byte as hostile input (12).

- The file is read, or mapped read-only, at any address. It is never mapped at `base_addr`, and never with `MAP_FIXED`.
- Pointers are translated as offsets from `base_addr`. A pointer that is outside the regions of the module and its loaded parts is a malformed input (exit code 4, 09.3). The root pointer of each part must point to an object, so a part that is cut after an object is also malformed.
- Every object header is checked: tag, field count, scalar size and total size, against the expected constructor of the Lean type at that position. The reader is typed: it knows that position p must hold an `Expr`, so a `Name` at that position is an error.
- The object graph must be acyclic. The reader decodes in post-order with an explicit stack and a visited table. A back edge is an error. In version 2 the compactor writes each object after its children, so the reader requires each pointer to point to an earlier object.
- A constructor without fields is a boxed scalar, also for a type with computed fields. For example `Level.zero` is box(0), as `Name.anonymous` is.
- Cached data is ignored and recomputed: `Expr.Data` (hash, flags, loose bound variable range, depth), `Level.Data` and `Name.hash` (D§3). The one exception is the cached `Name.hash` of the keys of the constant trie of version 4, which the reader compares with its own hash, because Lean uses it for the search. The 32-bit hash changed in v4.37.0-rc1 (#16107), so cached data cannot even be compared across versions.
- Big numbers are decoded from the GMP or native encoding by the flag bit. Limbs are checked for a canonical form (no leading zero limb). The reader of this version reads only the GMP encoding, and the native encoding is a decline.
- Strings are checked for UTF-8 and for their stored length and character count.
- The reader takes only `ModuleData.constants` and `constNames` (D§5.4). Environment extensions are not read.
- The reader version table has one row per supported `(OLEAN_VERSION, profile)`. An unknown version is a decline. In this version the table has three rows: version 2, which Lean v4.33 to v4.36 write for modules, version 3, which v4.36 writes for regions with closures, and version 4, which v4.37.0-rc1 writes. The profile comes from the Lean version in the header (05.2), not from the format version.
- In versions 3 and 4, `data_size` must fit in the file and be a multiple of 8, the objects must fill the data exactly, and the closure section and the library table must follow the data and end the file. The kernel input has no closures, so a file with closures is a decline. A library table without closures is malformed.
- In version 4, `ModuleData` must have the 7 object fields of v4.37.0-rc1, and `constTrie?` must be `some`. Because Lean imports the constants from the trie, the reader checks that the trie and `constants` give the same map from names to constants. A node of the trie has one of the forms `leaf key val`, `inner key children` and `node key val children`. The root must be an `inner` node with the anonymous key. Each other key must extend the key of its parent by one component. Lean finds a child by binary search on the cached `Name.hash` of the keys, and it computes the hash of the name that it looks up. So the cached hash of each key must be the hash that Lean computes (MurmurHash64A with seed 11 for the strings, and `mixHash`), the children must be sorted by this hash, and two children cannot have the same key. Each value must be the object of `constants` at the same index as its key in `constNames`, and the trie must have a value for each name of `constNames`. A node that occurs two times is malformed. With these rules, the search of Lean finds exactly the constants that the reader gives to the checker. The reader only checks that the pointer of `extraConstTrie?` is valid, because it holds names of compiler data.

### 07.3.4 Module order and parts

- The reader loads the import closure in topological order, from `ModuleData.imports`.
- For each module it loads `.olean`, then `.olean.server`, then `.olean.private`, as the official loader does.
- Where a theorem appears as an axiom in `.olean` and as a theorem in `.olean.private`, the private version is the declaration that is checked, and the axiom form must have the same name, level parameters and type.
- A module that is not a `module` file has a single `.olean`. That file holds full declarations.
- A private part can have no objects. Lean writes it so when the private data is the same as the public data, and its root is then the root of the public part. So a root can point into an earlier part.
- Lean can make the same auxiliary theorem in two modules, for example an equation lemma or an `induct_unfolding` lemma. The import of Lean (`finalizeImport`) accepts a second constant with the same name when one of the two constants subsumes the other (`subsumesInfo`). The two constants must have the same name and level parameters and the same type by the `==` of `Expr`, which is `Expr.eqv`. This test ignores the binder names and the binder info, so the reader compares the types with `expr_equal` of the checker and not by the handle. Two modules of Mathlib each declare an instance `CategoryTheory.Abelian.instIsStableUnderCobaseChangeMonomorphisms`, and the two types are not the same handle. The reader found this on the corpus run of Mathlib. The reader does not keep the metadata of an expression, so two types that differ only in metadata are equal for the reader and not for Lean. A theorem keeps its type and its value, so this has no effect on what the checker accepts. Then a theorem subsumes a theorem with the same `all` list, a theorem subsumes a safe axiom when its `all` list is its name, and an axiom subsumes an axiom with the same safety when the test `isPropCheap` shows that the type is a proposition. The values are not compared. When the later constant subsumes the earlier constant, the later constant replaces it, so the last copy wins. The reader does the same. The value of the later copy can use a declaration of a later module, so after a replacement the reader sorts the declarations from the position of the replaced constant again. Any other name that occurs two times is a malformed input. In v4.37.0-rc1, Lean does not check two modules against each other when a direct import loaded both modules when it was compiled (`checkImportConflicts`), so Lean can accept two constants with the same name that neither subsumes, and it keeps the first. The reader checks each pair, so it is stricter here.
- `ModuleData.constants` is not in dependency order, and it holds the types, constructors and recursors of an inductive block as separate constants. The reader makes one `Induct` declaration for each block, at the position of its first type. It puts each unsafe or partial definition into one `Mutual` declaration with the other definitions of its `all` list (04.7), because Lean adds a recursive unsafe or partial definition with `mutualDefnDecl`, and the olean does not keep the declaration form. An unsafe or partial definition that is not in its own `all` list did not come from `mutualDefnDecl`, so the reader gives it to the checker as a single definition, and `add_definition` checks it as the official kernel does for `defnDecl`. Mathlib makes such definitions: `compile_inductive` adds a copy of a definition with a new name and keeps the `all` list of the original (`Mathlib/Util/CompileInductive.lean`). Then a depth-first sort puts each declaration after the declarations of the module that it uses. The order of the recursors of a nested block can differ from the order in lean4export, and the checker finds recursors by name.

### 07.3.5 Trust

The `.olean` reader is not in theorem T1 for release 1.0 (10.1). It is in the "hardened, tested" class:

- It is written in safe Rust, with `#![forbid(unsafe_code)]` except for the mapping call in `rulean-io`.
- It is fuzzed (11.5) and runs under the resource limits of 12.3. The fuzz target `olean` in `fuzz/` gives the bytes of the parts of one module to `decode_parts`, which has the same checks as the load from files.
- It is cross-validated (07.3.6).

### 07.3.6 Cross-validation

For each corpus project and each profile, CI runs:

1. lean4export to NDJSON, then rulean on the NDJSON;
2. rulean directly on the oleans;
3. a comparison of the two decoded declaration streams, constant by constant, by structural hash.

Any difference is a release blocker. This is the evidence for the reader until it has a specification.

- lean4export gives a subset of the constants of the oleans. It does not export some auxiliary constants, for example `_unsafe_rec`, `_proof_N` and `_impl` constants. For Init of v4.36.0 the export has 58,547 declarations and the oleans have 64,714 before the mutual blocks are made. So the comparison requires each declaration of the export to be in the oleans, and it reports the others as a count.
- lean4export shares expressions that are equal up to alpha equivalence, because the equality of `Expr` in Lean ignores binder names and binder information. So a binder name in the export can come from another term. The comparison is modulo binder names and binder information.
- The first form of this check is the example `olean_compare` of `rulean-olean`. On Init of v4.36.0, each of the 58,547 declarations of the export is equal to the declaration from the oleans. Before the reader followed the replacement rule of 07.3.4, the check found 4 differences: the reader kept the first copy of 4 auxiliary theorems, and Lean keeps the last copy.
- The script `scripts/olean-xval.sh` runs the three steps on the modules of one Lean release, Init and Std by default. The CI job `olean-xval` runs it on v4.35.0 and v4.36.0, which have the profile v4.35 and write oleans of version 2, and on v4.37.0-rc1, which writes oleans of version 4. v4.37.0-rc1 needs the profile v4.37, and this profile comes in M7. Until then, the job sets `NO_PROFILE=1` for v4.37.0-rc1: `rulean check` must decline the export with `unsupported-version` and the exit code 2, and `rulean olean --parse-only` must load the oleans. The comparison with olean_compare is the same for each release. A difference or a declaration that is only in the export makes the job fail. The profile `master` and the corpus projects are not in the job.
- On Std of v4.36.0, each of the 96,627 declarations of the export is equal to the declaration from the oleans, and the oleans have 12,558 other declarations.
- The script `scripts/corpus.sh` runs the three steps on Mathlib, CSLib and Cedar at the commit of the Arena test. The weekly workflow `corpus` runs it on a GitHub-hosted runner (11.2). The step olean_compare reads the export as a stream, so its memory does not include the full export text.

## 07.4 Formats rulean does not read

| Format | Reason |
|---|---|
| `.ilean`, `.ir`, `.c` | not kernel input |
| Lean 3 `.olean` | out of scope (02.5) |
| `.olean` from releases before v4.35.0 | out of scope (02.5) |
| Dedukti, Lean4Less output | different logic; a later research option |
