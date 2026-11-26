# 06. The kernel inside `lean`

This section is for target G4: the kernel time of `lake build Mathlib` with rulean as the kernel must be at most 383 s, one tenth of the C++ kernel. Today it is 6987.2 s (03.6). The design of spec 09.6 stays: `lean` calls rulean through the C ABI, and rulean keeps a mirror of the Lean environment.

## 06.1 Where the time goes

From 03.6:

| Part | Time | Share |
|---|---|---|
| the checks again | 3332 s | 47.7% |
| the first check of each declaration | 2963 s | 42.4% |
| the mirror | 503.6 s | 7.2% |
| conversion of the declarations | 173.5 s | 2.5% |
| conversion of the results | 15.1 s | 0.2% |

So the order of the work is: remove the checks again (06.2), make the check fast with engine F (06.3), and then make the mirror and the conversion small (06.4, 06.5).

## 06.2 Look up at first use

Today the kernel finds a stale or a missing constant only after a pass, and then it checks the declaration again. The new design finds it at the first lookup, and the check does not run again.

1. At the start of `add_decl`, each name of the mirror is "not known" (`Env::known_reset`, as today).
2. The core looks up a constant through a source. The source is a generic parameter of the checker with one method: give the constant for a name. The core stays in the Aeneas subset, because a trait with a generic parameter is in the subset (spec 10.6) [U for the exact Aeneas rule; the twin must accept it].
3. The source of the FFI does this for a name that is not known: it finds the `ConstantInfo` in the Lean environment of the call. If the mirror has the same object, the name becomes known. If the mirror has another object, or no object, the source converts the object and puts the constant in the mirror. Then the name becomes known.
4. If Lean has no constant with the name, the lookup fails, and the check gives the same error as the C++ kernel.

So each lookup of a check sees the Lean environment of the call. The result is the same as the result of the last pass today, with one pass.

The pass limit (`PASS_HEARTBEATS`, `PASS_GROWTH`) is there because a pass with a stale constant can take a long path. With a lookup at first use, no check sees a stale constant. So the check has one pass with the limit of the call, and the pass loop is removed.

Proof: the source is outside the core. The core lemma is: if each lookup gives the constant of the environment E, then the check gives the result of a check on E. The twin has this lemma for a fixed environment today (spec 10). The new part is the lemma that a source that adds constants during the check gives the same result as an environment that has them from the start. The constants that the source adds are not checked, as today.

## 06.3 Engine F in-process

The in-process kernel uses engine R today. After 04 (milestone M9), engine F is the default for the external check. Then the in-process kernel uses engine F too, with these rules:

- The heartbeat rule of spec 09.6.4: rulean must not count more heartbeats than the C++ kernel on a declaration that the C++ kernel finishes. Engine F counts its steps with the same weights as engine R. Calibration 2 of 09.6.4 is done again with engine F on the dual-kernel build.
- The dual-kernel build compares the two kernels on each declaration, as today. A declaration where the two kernels do not agree stops the merge of the change.

## 06.4 The mirror

The mirror converts 313.7 s of imported constants. Most of the imported constants are never used by a check in the same process [U]. With the lookup at first use (06.2), the mirror converts a constant only when a check looks it up. The walk that loads the constants before a check (`walk` with `PRELOAD_DEPTH`) is then not needed for the result. It stays only if a measurement shows that it is faster than the lookup at first use.

The conversion of a constant keeps a memo from the address of a Lean object to the store handle, for each `lean` process. A term that two constants share is then converted once.

## 06.5 Conversion of the declarations

The conversion of a declaration uses the same memo as the mirror. The conversion of the results (15.1 s) is small, and it does not change.

## 06.6 Budget

The budget for G4 is 383 s:

| Part | Budget |
|---|---|
| the checks again | 0 s |
| the check, with engine F | 250 s |
| the mirror | 80 s |
| conversion of the declarations and the results | 40 s |
| margin | 13 s |

The check budget needs engine F to be about 12 times faster than engine R on the declarations of Mathlib. This is the same factor as on Init (04.10).

## 06.7 Threads in-process

`lean` runs the elaboration of one file on more than one thread, and each thread can call the kernel. The mirror has a lock today. The kernel time of G4 is summed over the threads, so the lock does not change the measure. A lock that waits for a long time adds wall time. The time in the lock is measured (spec 08.6) before a change to the lock is made.

## 06.8 What does not change

- The C ABI of spec 09.6.
- The error messages and the exceptions of spec 09.6.2.
- The rule that rulean never accepts a declaration that the C++ kernel rejects, on the dual-kernel build.
