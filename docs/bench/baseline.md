# Baseline of the official kernel

This file records the baseline of spec 08.7.1: the official kernel of Lean v4.35.0 (`leanchecker --from-export`) on the tests of the Lean Kernel Arena, compared with the numbers that the Arena publishes. The `bench` workflow makes these numbers. The M0 exit criterion of spec 14 says that our counts must be within 2% of the Arena counts.

## Run of 2026-11-21

| Fact | Value |
|---|---|
| Workflow run | [44912719616](https://github.com/tamnd/rulean/actions/runs/44912719616) |
| Machine | GitHub-hosted `ubuntu-latest`, x86-64 |
| Counter | valgrind cachegrind, `--cachegrind-max 5` |
| Arena data | commit dbb57ce of 2026-11-21 10:15:45 UTC, `results.json` SHA-256 0dc68ce0 |
| Tests | 225 in the tarball, 225 with the hash of `results.json` |

### Verdicts

All 225 tests gave the verdict of the Arena: 225 correct, 0 incorrect, 0 declined, 0 error.

### Instruction counts

212 tests have a count on both sides. The other 13 tests ran for more than 5 seconds, so the job did not count them with cachegrind.

| Measure | Value |
|---|---|
| Sum of the Arena counts | 145.567 G |
| Sum of our counts | 147.254 G |
| Ratio of the sums | 1.0116 |
| Tests within 1% | 5 |
| Tests within 1% to 2% | 1 |
| Tests above 2% | 206 |
| Largest deviation | 42.2% (`perf/gf3-matrix-product`) |

The deviations have two causes:

1. **A fixed offset on each run.** On each small test, cachegrind counts about 19.5 M instructions fewer than the Arena. The Arena counts about 190 M and cachegrind about 171 M, so the ratio is 0.897. Most of the Arena tests are small, so most tests are above 2%. A probable cause is the start of the process. The Arena runs `perf stat` over GNU time and `sh -c`, and cachegrind starts to count later than `perf`. This is [U].
2. **A different count of some instructions.** On the large tests, the ratio is between 0.97 and 1.025, except `perf/gf3-matrix-product` at 1.42. Cachegrind and the CPU do not count all instructions in the same way, for example the steps of a `rep` instruction. This is [U].

### Result

The verdicts match. The counts of cachegrind are not within 2% of the Arena counts, so cachegrind cannot give the baseline. The baseline needs `perf stat -e instructions:u` on a Linux x86-64 machine that exposes the hardware counters, as the Arena does. The workflow can use such a machine with the `counter` input set to `perf`. Then it applies the 2% limit.

Cachegrind stays useful for a trend: it gives the same count on each run, so it can show a change of rulean from one commit to the next on the same runner.
