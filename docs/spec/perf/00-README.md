# Performance spec

This part of the spec sets the performance goal of rulean and the plan to reach it. It adds to spec 08 and does not replace it. Where the two disagree, this part has priority, because it is newer and it uses newer measurements.

## Goal

rulean must be at least 10 times faster than each popular Lean 4 kernel on the same input. Section 01 defines "popular", "faster" and the corpora. It also gives the targets as numbers.

## Files

| File | Content |
|---|---|
| 01-goal.md | the goal, the popular kernels, the measure, the targets |
| 02-research.md | the other kernels and the techniques that make them fast, with sources |
| 03-rulean-today.md | the measurements and the profiles of rulean in November 2026 |
| 04-architecture.md | the new design of the check, from first principles |
| 05-input.md | the new design of the read and the parse |
| 06-in-process.md | the new design of the kernel inside `lean` and `lake build` |
| 07-plan.md | the milestones, the work items, the gates and the releases |
| 08-where-time-goes.md | the measures of Init after the first M9 steps, and the work that follows |
| 09-rivals.md | what the fastest rivals do, and the changes to engine F that follow |
| 10-engine-g.md | engine G, the machine for closed terms, the step `ground_cmp`, and the next work |

## Rules for this part

1. Each number has a source. A number that we measured has the command, the machine and the date. A number from another project has a URL.
2. A guess is marked [U]. A guess is not a reason to merge a change. A measurement is.
3. Speed never changes a verdict. Each change keeps the soundness rules of spec 05.1 and the parity rules of spec 11.
4. The core crates stay in the Aeneas subset (spec 10.6). A technique that needs code outside the subset goes into a crate outside the core, or it is not used.

## Copies

This part has two copies with the same text: `docs/spec/perf/` in the repository and `2148l/perf/` in the notes. A change to one copy is also a change to the other copy.
