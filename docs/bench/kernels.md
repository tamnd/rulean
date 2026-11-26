# rulean and the popular kernels

This file records the counts of `scripts/kbench.sh` (spec perf/07.3) for rulean and the popular kernels of spec perf/01.2. Each count is for one thread on one machine. Use the counts for a ratio between two kernels. The Arena counts are on another machine, with `perf` and with more threads for some kernels.

## Run of 2026-11-25

| Fact | Value |
|---|---|
| Machine | Apple Mac, 10 cores, 24 GB, load average 35 to 87 |
| Counter | `/usr/bin/time -l`, "instructions retired" |
| Toolchain | Lean v4.36.0 |
| rulean | commit bd14f4b, release build |
| Export | `init.ndjson` of the Arena test `init`, 348 MB, 6495296 lines, 58547 declarations |

| Kernel | Exit code | Instructions | Peak memory | Arena count |
|---|---|---|---|---|
| rulean, engine R | 0 | 242.2 G | 462 MB | none |
| nanoda | 0 | 247.0 G | 548 MB | 223.8 G, 4 threads |
| official `leanchecker` | 0 | 410.9 G | 575 MB | 401.5 G, v4.35.0 |
| rulean, engine F | 0 | 437.0 G | 455 MB | none |
| con-ron | 0 | 566.0 G | 773 MB | 172 G, `--verified --jobs=4` |

The local counts of nanoda and the official kernel are within 10% of the Arena counts. rulean engine R uses 1.70 times fewer instructions than the official kernel and 1.02 times fewer than nanoda. The target G2.a of spec perf/01.4 is 22.4 G.

## Run of 2026-11-26

The same machine and toolchain, on `init-prelude.ndjson` of the Arena (3.8 MB).

| Kernel | Exit code | Instructions | Peak memory |
|---|---|---|---|
| nanoda | 0 | 0.963 G | 14 MB |
| rulean, engine R | 0 | 0.992 G | 14 MB |
| rulean, engine F | 0 | 1.134 G | 17 MB |
| official `leanchecker` | 0 | 2.439 G | 64 MB |
| con-ron | 0 | 3.630 G | 35 MB |
