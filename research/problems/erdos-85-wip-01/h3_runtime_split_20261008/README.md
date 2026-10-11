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

## Production canary verified

Job `20261008T115843-erdos85__h3-triple-formal-20261007-474713` exited zero
at `1f0129e035f2161d32a147a316c43f3d433b5fe8`. Compiling the production
Runtime's exported shared library took 0.965 seconds. With that plugin,
the unchanged `triplePart 384 0 = true` theorem compiled in 31.355 seconds
(30.119 seconds child user time; maximum child RSS 6,486,088 KiB).

The earlier optimized, unsplit engine took 143.890 seconds on the same
bucket and source theorem. This single comparison is about 4.59 times faster
by Lean elapsed time, excluding the shared-library compilation. Phase three
remains in the Mathlib-importing Engine, so the 13.15-fold standalone
phase-two speedup is not an estimate for this full computation or other
buckets.

The result uses exactly `propext`, `Quot.sound`, and
`Erdos85.H3TripleCompletion.triplePart_384_0._native.native_decide.ax_1_1`.
Its 6,712-byte object has SHA-256
`f41f84072713f0b4baec2698955ed25a95bad7d5fe5fae7ef504fa2e96dc3959`.
The production shared library has SHA-256
`1d58071a6732bd981763acae6ccd916f2e43ecdffdedbbd6b3ed182d9810cc95`.

`canary-evidence` retains the raw job records, runner, unchanged probe,
prerequisite audit, timing receipt, symbol table and axiom output. The
read-only collector verifies the successful terminal exit, exact execution
sources, unchanged prerequisite objects and Runtime C, nonempty result
object, artifact hashes and exact part axiom set. The compiled objects and
shared library remain on the builder.

This revalidates the existing bucket after a soundness-preserving refactor.
It does not add another verified bucket: 383 of the 384 premises are still
unverified. No full-campaign runtime estimate or launch follows from this
single measurement.
