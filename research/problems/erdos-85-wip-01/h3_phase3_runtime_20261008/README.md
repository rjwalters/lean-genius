# H3 phase-three runtime helpers

The first production runtime split reduced the existing bucket-zero test
from 143.89 to 31.36 seconds. This follow-up moves four more executable
declarations verbatim into the Std-only runtime: `cands3`, `gate3`, `pick3`
and `addMany`. The recursive phase-three search and its Mathlib combination
enumeration stay in the Engine. Search order, guards and proof bodies are
unchanged.

`MOVE.json` and `verify_move.py` check all 49 moved declarations against the
original unsplit source at `2f41a16de17`, and verify that all remaining
non-comment source tokens match. The preceding 45-declaration stage and its
evidence remain under `../h3_runtime_split_20261008/`; its current-source
checker is tied to that historical stage.

This change requires a fresh Runtime/Engine/Bridge/Split build and a new
bounded plugin check of the existing bucket `triplePart 384 0 = true` before
any timing or validation result is credited. No other bucket is run and no
whole-cell exclusion is claimed.

## Conditional build

Job `20261008T120308-erdos85__h3-triple-formal-20261007-477911` exited zero
at `a64f02c30eafde63acece8f251fd98666b757ea7`. Runtime, Engine, Bridge and
Split freshly built in 1.5, 9.1, 4.7 and 3.7 seconds. The four printed
soundness exports use exactly `propext`, `Classical.choice`, `Quot.sound`.
No `sorry` or additional assumption was found. `build-evidence` binds the
exact sources, fresh objects, Runtime C and terminal job records.

`run_canary.py` uses that exact Runtime C, preserves the production probe
source, and verifies prerequisite hashes before compiling the exported
library and running the existing bucket-zero theorem. Caps remain 60
seconds for the library, 180 seconds for Lean, four minutes for the outer
job, two CPUs and 16 GiB. No full campaign is launched.

## Bucket-zero result

Job `20261008T120507-erdos85__h3-triple-formal-20261007-479545` exited zero
at `9739de63467971b3c0ba673fd4ea2bbcac0c608b`. The exported runtime library
compiled in 1.115 seconds; the unchanged production bucket-zero theorem
compiled in 15.132 seconds (13.927 seconds child user time, maximum child
RSS 6,488,492 KiB). Neither stage hit its cap.

The previous 45-declaration runtime stage took 31.355 seconds on this bucket;
the earlier optimized unsplit engine took 143.890 seconds. This comparison
shows about a further 2.07-fold reduction and about 9.51-fold overall by Lean
elapsed time, excluding library compilation. One selected bucket does not
establish a runtime bound or estimate for the other 383 parts.

The result retains exactly `propext`, `Quot.sound` and
`Erdos85.H3TripleCompletion.triplePart_384_0._native.native_decide.ax_1_1`.
Its 6,712-byte object has SHA-256
`ff32a8d24924124f1db178025c7feb269acb69d55b00e57d53a19620d08b48f9`.
The runtime library has SHA-256
`34da36a0730f0dfc6dd6d5c9f2cf47119b1ee8fe86e95a606067546422e6cdeb`.

`canary-evidence` retains the exact probe, runner, prerequisite audit,
terminal job records, timing receipt, exported-symbol table and axiom report.
The read-only capture verifies unchanged source/object prerequisites,
generated Runtime C, library/result hashes and exact part axiom set. Objects
and library remain on the builder. Only the existing bucket is reverified;
the ledger remains one verified part of 384.
