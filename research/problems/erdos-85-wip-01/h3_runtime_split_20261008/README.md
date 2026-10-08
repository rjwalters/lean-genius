# Production H3 runtime split

The standalone benchmark in `../h3_precompiled_probe_20261008/` found a
13.15-fold phase-two traversal speedup after precompiling a Std-only runtime.
This change moves those same 45 executable declarations into the production
`Proofs.Erdos85H3TripleCompletionRuntime` module. The Engine imports it; the
Bridge and Split receive it transitively. All names and declaration bodies
are preserved. Phase three remains in the Engine.

`MOVE.json` binds the old source at `2f41a16de17`, the 45 declaration bodies,
and the revised source hashes. `verify_move.py` checks each moved declaration
verbatim, then verifies that all remaining non-comment source tokens match
the previous files after removing the moved declarations and new import.
It invokes no Lean computation.

The source comparison is not the soundness validation. The revised
Runtime/Engine/Bridge/Split chain must compile successfully, with the existing
soundness exports retaining their standard axiom sets. A plugin test must
then use the generated C from that exact production Runtime and the existing
bucket-zero source. No additional bucket or whole-cell credit is asserted
by the relocation or by the earlier standalone benchmark.

## Conditional build verified

Job `20261008T115540-erdos85__h3-triple-formal-20261007-472600` exited zero
at `3247ac5b9e10d688214d3de9f5f0a2d6442dc087`. Runtime, Engine, Bridge and
Split were freshly built in 1.4, 9.8, 4.0 and 3.9 seconds. All four soundness
exports retained exactly `propext`, `Classical.choice`, `Quot.sound`, with no
`sorry`. `build-evidence` retains the exact sources and raw job records;
the read-only audit binds those to the fresh objects and generated Runtime C.
The first observation arrived before the terminal exit record; the later
successful audit inspected the same job, without a restart.

`run_canary.py` compiles that audited Runtime C with Lean's exported-symbol
flag and loads the resulting plugin for the existing `Probe384R0.lean`.
It checks all prerequisite source/object hashes before running, uses a
60-second shared-library compile cap and a 180-second Lean cap, and records
the exact commands, artifacts and raw reports. The outer cloud job is capped
at four minutes, two CPUs and 16 GiB. It reruns only the already verified
bucket zero; other bucket premises remain outstanding.
