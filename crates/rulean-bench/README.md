# rulean-bench

`rulean-bench` runs a checker on each test of a corpus and records the instruction count, the wall time, the CPU time and the peak memory of each run. The results are in the format of the [Lean Kernel Arena](https://arena.lean-lang.org/), so you can compare them with the Arena numbers. The method is in spec section 08.7.

## Run

The command after `--` runs once for each `.ndjson` file under the test paths. `{}` in the command is the path of the export. The variable `IN` also holds it, as in the Arena.

```sh
cargo build --release -p rulean-bench
target/release/rulean-bench run --checker official --timeout 300 --out official.json arena-tests -- leanchecker --from-export {}
```

The test layout is the layout of the Arena test tarball. A file under `good/` must be accepted and a file under `bad/` must be rejected. The test name is the path under `good/` or `bad/` without the extension, for example `tutorial/011_nonTypeAxiom`.

The exit code of the checker gives the status: 0 is `accepted`, 1 is `rejected`, 2 is `declined`, and other codes are `error`. A run that passes the timeout is `timeout`.

## Counters

| Counter | Where | Measure |
|---|---|---|
| `perf` | Linux with hardware counters | `perf stat -e instructions:u`, the measure of the Arena |
| `cachegrind` | Linux with valgrind | the `I refs` of cachegrind, from a second run; about 50 times slower |
| `rusage` | macOS | `instructions retired` of `/usr/bin/time -l`; includes the system calls |
| `none` | all | no count |

`--counter auto` (the default) selects `perf` if it gives a count, then `cachegrind`, then `rusage` on macOS. GitHub-hosted runners do not expose the hardware counters, so `perf` does not work on them. With `cachegrind`, `--cachegrind-max SECONDS` counts only the tests whose first run took at most that time, so that the large tests do not take hours. Compare only the numbers of the same counter on the same kind of machine. Only `perf` numbers can be compared with the Arena numbers.

The CPU time and the peak memory come from `/usr/bin/time`. On a machine without it, they are 0.

## Compare

```sh
curl -sSfLO https://arena.lean-lang.org/results.json
target/release/rulean-bench compare --base-checker official --tolerance 2 results.json official.json
```

`compare` prints the ratio of the counts for each test that has a count on both sides. It exits with code 1 if a test gives a different status on the two sides, or if a ratio differs from 1 by more than the tolerance in percent.

## Gate

```sh
target/release/rulean-bench gate --correct --max-rss-mib 4096 rulean.json
target/release/rulean-bench gate --filter perf/ --max-virtual-seconds 1 rulean.json
```

`gate` reads a run file of `run` and checks limits on each result. It prints one line for each failed limit and exits with code 1 if a limit failed or if no test matched the filter. `--correct` requires the expected verdict. `--max-virtual-seconds S` requires at most S times 6.0 G instructions, and a test without a count fails this limit. `--max-rss-mib N` limits the peak memory and `--max-wall SECONDS` limits the wall time. The second command above is the P1.d gate of spec 08.7.2.

The workflow `.github/workflows/nightly.yml` runs rulean through `scripts/arena-run.sh` on the Arena tests each night with the `cachegrind` counter, and then runs the two gates above. With `--cachegrind-max 5`, a test that takes more than 5 s has no count, so it fails the P1.d gate. This is correct, because such a test is far above 1 virtual second.

## Work

```sh
target/release/rulean-bench work docs/bench/work.json Init=init.json Std=std.json
```

`work` reads the JSON reports of `rulean check` and compares the work count of each report (`summary.steps` plus `summary.interns`) with the entry of the same name in the baseline file. It prints one line for each export and exits with code 1 if a count differs from the baseline by more than the tolerance in either direction (`--tolerance PERCENT`, 1 by default), if the Lean version of the report is not the version of the baseline, or if the verdict of the report is not accept. With `--write`, it writes the counts into the baseline file and does not compare. Use a sequential check (`--threads 1`), because its counts are the same on each machine. `scripts/work-gate.sh` runs this gate on Init and Std of a Lean release, and the CI job `lake comparator` runs the script. This is the quick suite gate of spec 08.7.4.

On macOS, the `rusage` counter counts only the process that `run` starts. If this process is a script that starts the checker, the count does not include the checker. Run the checker directly when you use `rusage`.
