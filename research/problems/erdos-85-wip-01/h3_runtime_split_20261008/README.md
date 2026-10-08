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
