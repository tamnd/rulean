# 08. Where the time goes on Init

This section gives the measures of the Init export after #216, and the work that follows from them. All counts are from the local measure of 07.3 with one thread, on the machine of 03 (Apple Mac, 10 cores, 24 GB), on 2026-11-27. The command is `rulean check --threads 1 --engine R|F --report /dev/null init.ndjson`, and the count is the `instructions retired` line of `/usr/bin/time -l`.

## 08.1 The two engines

| Engine | Instructions |
|---|---|
| R | 144.5 G |
| F | 208.6 G |

Engine F uses more instructions than engine R. The exit of M9 needs at most 80 G with engine F, so the gap is large.

## 08.2 Engine F per declaration

A probe gave the time of each value check with each engine. There are 57,934 value checks.

| Set | Count | Engine F | Engine R |
|---|---|---|---|
| Engine F accepts | 57,660 | 7.41 s | 7.61 s |
| Engine F stops | 274 | 1.83 s, then 2.47 s in engine R | 2.28 s |

When engine F accepts, it is only 3% faster than engine R. When engine F stops, the time of engine F is lost, and then engine R checks the declaration from the start.

All 274 stops have the fault `ArenaFull`. No stop comes from a query that engine F cannot answer.

## 08.3 The size of the arena

The arena has `MAX_NODES` values. The table gives Init with engine F for each size.

| `MAX_NODES` | Instructions | Stops |
|---|---|---|
| 2^14 | 182.5 G | 3,212 |
| 2^15 | 189.2 G | 2,135 |
| 2^16 | 193.7 G | 1,192 |
| 2^17 | 198.6 G | 574 |
| 2^18 | 208.6 G | 274 |
| 2^20 | 237.3 G | 62 |
| 2^22 | 272.3 G | 11 |

A larger arena gives fewer stops, but more instructions. Thus on the large declarations of Init, engine F uses more instructions than engine R, also when the time of the stop is added. The arena size is a budget, and engine R is the better engine for these declarations.

A small arena is not a fix. On the perf tests, a small arena makes the tests that need engine F much slower. With 2^14, `app-lam` goes from 0.2 G to 38.0 G, `beta-ladder` from 0.1 G to 10.1 G and `let-ladder` from 0.1 G to 5.2 G.

## 08.4 Value keys

The value keys of 04.12 use about 9% of the samples of engine F on Init. A run with no `c_unfold_key` used 249.7 G, so the cache gives more than it costs. A cap of 2^20 entries in `k_nodes` made `magma-list-deep-n21` slower (27.6 G against 21.1 G), so a cap is not a fix.

## 08.5 Engine R

About one third of the samples of engine R on Init are in `inst_rec`. These are the callers:

| Caller | Share of `inst_rec` |
|---|---|
| `whnf_core_app` (beta) | 51% |
| `infer_app` | 27% |
| `infer_lambda` | 15% |
| `infer_pi` | 3% |

The hash-cons walk `probe` and `mk_app` use about as many samples as `inst_rec`, and most of the new nodes come from `inst_rec`.

`infer_app` in check mode inferred the type of each partial application. For each argument, it instantiated the full body of the pi type. For a head with n arguments and a pi type of size S, this is O(n S). The fix infers the type of the head one time. It instantiates only the domain of each binder with the arguments before it, and it instantiates the body one time at the end. The checks and their order do not change.

## 08.6 Work that follows

1. `infer_app` in chunks (08.5). Engine R on Init goes from 144.5 G to 140.7 G.
2. A cheaper stop of engine F. The time of engine F before a stop is lost. A stop that comes earlier loses less time, but a small arena slows the tests of 08.3. A budget of steps that grows with the size of the declaration can stop early on large proofs and still let the small loops of the perf tests run.
3. Fewer new terms in engine R. Beta and `infer_lambda` make most of the new nodes. A cache of the instantiation of a body with the same arguments removes the nodes that are made again.
4. The 80 G exit of M9 is not in reach with these steps. Engine F is not faster than engine R on Init, so the default engine stays R until engine F is faster on Init and on the perf gate.
