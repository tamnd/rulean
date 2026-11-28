# 12. The check from first principles

The steps of sections 08 to 11 are small. Each step removes some work from a hot path, and the sum is real: Init with engine F went from about 93 G to about 85 G. But the target G2.a of section 01 is at most 22.4 G on Init, and small steps do not close a gap of 4 times. This section starts again from the cost of the work that a check must do, compares it with the work that rulean does, and gives a new design for engine F.

## 12.1 The cost model

The check of one declaration must do three things.

1. It must read the terms of the declaration.
2. It must infer the type of each subterm that the rules need, and it must reduce terms where a rule needs a head normal form.
3. It must compare two types where a rule needs them to be equal.

The rules do not need new terms. A new term is necessary only where the result goes out of the kernel, for example the type of a declaration that the session stores. All other terms that the kernel builds are a cost of the method, not of the rules.

Init has 58,547 declarations. The target of 22.4 G for Init gives a budget of about 380 k instructions for each declaration. Today engine R uses about 1.4 M instructions for each declaration. A hash-consed node costs about 60 to 100 instructions to make (hash, probe, compare, write). So the budget is about 4000 new nodes for each declaration, if the check does nothing else. Today the check makes about 1530 new nodes for each declaration, and the other work (walks, probes, reduction) costs more than the nodes.

## 12.2 What rulean does today

All counts are from `rulean check --threads 1` on Init, after #259, on the machine of section 03. The profiles are from `sample` with a build that has debug symbols.

### Engine R

Engine R checks with substitution on hash-consed terms. On Init it makes 89.8 M new interned nodes, which is about 1530 nodes for each declaration on average, and much more for the large ones. It makes 10.5 M calls to `instantiate`: 3.46 M forward and 7.05 M reverse.

| Function | Samples (of 5806 in the check) |
|---|---|
| `intern_expr` | 1532 |
| `inst_rec` | 1815 |
| `probe` (self) | 1134 |
| `promote` | 561 |

The callers of `inst_rec` are `whnf_core_app` (752), `infer_lambda` (522), `infer_app` (325) and `infer_pi` (150). Thus the beta step and the inference of binders make most of the new terms. The probe of the hash table is the largest self cost, because the table is large and each probe is a cache miss.

### Engine F alone

To see the cost of engine F without engine R, we made a probe binary where engine F checks each value and each type. It is not merged. Init gives 204.2 G, with 121 M interns, 483 M steps, 832 queries to engine F that fail over, and 15516 confirms by engine R.

| Function | Samples (of 13933 in `check_export`) |
|---|---|
| `f_infer` | 10939 |
| `f_conv_top` | 8006 |
| `conv_spines` | 6390 |
| `unfold_glued` | 3453 |
| `conv_delta` | 3248 |
| `force` | 3135 |
| `iota_value` | 3027 |
| `eval` | 2795 |
| `is_def_eq` (engine R inside engine F) | 2512 |
| `spine_key` and `key_node` | 2928 |
| `quote` | 1195 |

Two facts are important.

1. Engine F also builds terms. The callers of `mk_app` are the parse (994), `inst_rec` (559), `quote` (354), `whnf_core_app` (312), `lps_rec` (224), `unfold_definition` (140) and `promote` (138). `unfold_glued` instantiates the levels of a definition body as a new term and then evaluates it. `quote` reads back a value as a term. Engine R inside engine F does its own substitution.
2. Engine F makes a new value for each node that it evaluates, and the values are not shared. To find equal values for its caches, it computes a key of each value with a recursive walk (`spine_key`, `key_node`). These keys cost about 21% of the samples.

So engine F pays twice. It allocates values that are not shared, and then it pays to find the shared ones.

## 12.3 What the fastest rivals do

Section 09 describes the rivals. The principles that matter here are below. The sources are the yaml files of the Arena checkers and the papers and posts that section 02 lists.

1. Gruszka does not build terms in the check. Values, environments and spines are hash-consed when they are made. The head normal form and the type of a value are cached in the value. An argument that its binder never reads is not evaluated. A `casesOn` reduces only its major premise. It keeps one session across declarations, it uses regions with an undo log to free the work of a declaration, and it changes to a call-by-need machine when a declaration makes more than 2^26 values.
2. nano-lean hash-conses its values. It has an eval cache at the key (term, level substitution, environment). Its closures keep only the variables that the body reads, with a 32-bit mask. Each value has its own memo slots.

Both rivals are near 24 G on Init. Both use the same three ideas: no new terms, shared values with an O(1) key, and memos in the value.

## 12.4 The new design

The design has six parts. Each part is one or more work items in issue #260. Each part is measured alone and is merged only if it helps.

### P1. No term in the hot path

`eval` takes a level substitution as an argument, in place of `instantiate_value_lparams` on the term. `unfold_glued` evaluates the body of the definition with the levels of the constant, and it does not make a new term. The inference returns values. A read-back to a term happens only for a fault, for the type that the session stores, and for a query that goes to engine R.

### P2. Shared values

The arena interns each value, each environment node and each spine node when it is made. The hash of a node is O(1), because it uses the ids of the children, which are already interned. Then two equal values have the same id, and the id is the key. The recursive keys `spine_key`, `key_node` and `env_key` are removed. The table of the arena has a mark for each declaration, and the release of the arena truncates the table at the mark, in the same way as `Memo::truncate`.

### P3. Memos in the value

Each value gets slots for its head normal form, its weak head normal form without delta, and its type. A query reads the slot first. The slots are in a side array of the arena with the same index as the value, so a slot costs no hash.

### P4. Trimmed closures

A closure keeps only the part of the environment that the body reads. The term gets a mask of its loose bound variables when it is interned. With P2, two closures that read the same values are the same closure, so the caches find them.

### P5. An eval cache

`eval` keeps a cache at the key (term, level substitution, environment id). With P2 and P4, the key is three ids, and many calls find a hit.

### P6. Regions

The work of one declaration goes into a region. At the end of the declaration, the session keeps the values that it needs and releases the region with one truncate. This replaces the current `promote` walk for the values of engine F.

## 12.5 The order of the work

| Step | Part | Measure |
|---|---|---|
| 1 | P2 for spines and environments, keys removed | interns, steps, Init with engine F |
| 2 | P2 for values | the same |
| 3 | P1 for `unfold_glued` (levels in `eval`) | `mk_app` calls from `lps_rec` and `unfold_definition` |
| 4 | P3 for whnf and type | `force` and `f_infer` samples |
| 5 | P4 and P5 | `eval` samples, hit rate |
| 6 | P1 for the inference (values out, no `quote` in the hot path) | `quote` samples |
| 7 | P6 | `promote` samples, peak memory |

Step 1 comes first because the keys are a large cost with a clear removal, and because P3, P4 and P5 need the ids of P2.

## 12.6 Measurement

The machine of section 03 is shared with other work, and in November 2026 it has a high memory pressure. The count of instructions for the same binary changes by up to about 15% between runs, and the peak memory changes from about 530 MB to about 970 MB. Thus each comparison uses runs of the two binaries in turn, and it uses the minimum. Each PR also gives the counters in the report, which do not change between runs: the count of interns, the count of steps and the count of queries.

## 12.7 Results that did not help

The results of 11.21 apply here. A cache of whole calls to `instantiate` made more work than it saved, because the memo of `inst_rec` already finds most of the repeated nodes. This supports P1: the gain is to make fewer terms, not to find the terms that we made before.

## 12.8 Results of step 1 and of the tiers

### Step 1 did not help

Step 1 of 12.5 interns each spine and each environment in the arena, removes the value keys, and keeps the cache of `unfold_glued` in the slot of the value. The branch is not merged. The results on Init are the minimum of interleaved runs.

| Build | Mode | Init (instructions) |
|---|---|---|
| main at #259 | default | 85.7 G |
| step 1, full hash table | default | 86.9 G |
| main at #259 | engine F alone | 202.9 G |
| step 1, full hash table | engine F alone | 243.3 G |
| step 1, direct-mapped table of 4096 entries | engine F alone | about 274 G |

In the default mode the change is about 1.2 G slower. With engine F alone it is 42 G slower, and the direct-mapped table makes it worse, because the misses make more values. The shared slots also change the work of engine F: the count of steps goes up by about 7%, and engine R confirms more results. A shared value has one slot, but the same value in two contexts can need two different cache entries. Thus P2 in this form is not a gain. The keys cost less than the intern of each spine and each environment.

### Engine R does most of the check

In the default mode, engine F checks only small values and deep types, so engine R checks nearly all of Init. The counters of a probe binary give these counts for engine R on Init.

| Counter | Count |
|---|---|
| interns | 91.7 M |
| walks | 61.3 M |
| walks of the frozen tier | 26.2 M, with 12.8 M hits |
| walks of the scratch tier | 35.1 M, with 2.8 M hits (8%) |

The scratch tier finds only 8% of its walks. The profile of 12.2 shows that `inst_rec` is about 31% of the check and the probes of the large tables are about 23%. If all the cost of `instantiate` went away, Init would be about 55 G. Thus the target of 22.4 G needs a change of the whole check, not a change of one part. The two possible paths are these.

1. Engine R makes fewer terms in `infer_lambda`, `infer_app` and the beta step, and it probes smaller tables.
2. Engine F becomes able to check all of Init with less work than engine R, so that the default mode can use it for each declaration.

### A smaller scratch table did not help

A branch made the scratch table and the memo smaller when they are cleared after a declaration (a factor of 8, with a minimum of 2^14 slots). The goal was fewer cache misses. Init with engine R went from 80.1 G to 82.2 G and 83.6 G for the two variants, and the cycles did not show a clear gain. The branch is not merged.

## 12.9 Where engine R makes its terms

A probe binary (not merged) counts the interns at each site that instantiates a term, on Init with one thread, after #264. The total is 90.3 M interns.

| Site | Interns | Calls |
|---|---|---|
| beta in `whnf_core_app` | 28.5 M | 3.79 M |
| `infer_app_check` | 12.4 M | 11.15 M |
| body of `infer_lambda` | 10.8 M | 0.26 M |
| abstraction of the type in `infer_lambda` | 4.3 M | 0.26 M |
| body and domains of `infer_pi` | 2.2 M | 0.72 M |
| other calls of `instantiate_rev` | 1.5 M | 0.46 M |
| domains of `infer_lambda` | 0.5 M | 0.50 M |
| levels of constants (type and value) | 0.8 M | 0.63 M |
| `let` in `whnf_core` | 0.2 M | 0.02 M |

The other interns (about 29 M) come from `unfold_definition`, `promote` and the other functions that make terms. A sample of 25 s of the check gives these inclusive counts, of 9100 samples in `check_export`.

| Function | Samples |
|---|---|
| `lazy_delta_reduction_step` | 3795 |
| `inst_rec` | 3455 |
| `whnf_core_app` | 3206 |
| `mk_app` | 3192 |
| `probe` | 1894 |

Thus the construction of terms is about half of the check, and the beta step of the lazy delta reduction is the largest part of it. The table probe is mostly one cache miss on the first slot, because the slots keep the hash and the walk reads the node only when the hash is the same.

Inference on open terms (no instantiation of the body of a binder) can remove at most the body and the abstraction of `infer_lambda` and the body of `infer_pi`, which is about 16 M interns (18%). Some of this cost comes back, because a dependent argument must be closed before it goes into the type. The beta step stays. So this change alone cannot give the target of 12.1. The beta step of the lazy delta reduction makes a full term for each unfolded definition, and most of these terms are used only for one comparison. A design that reaches the target must make the comparison without these terms. Engine F does this with values, but 12.8 shows that today it does more work than engine R.
