# Static single-column pruning diagnostic

One fixed full-template pair: compact U code `(6,6,15)` and R representative14,
the pair used by the squad's kernel-verified cross canary. No cross enumeration
or terminal search is performed here.

Compact column-list sizes: `[1,75,75,75,125,125,125,125]` (726 total entries).
Static C4-filtered sizes: `[1,36,36,36,15,15,15,15]` (169 total entries).
The retained Lean run measured23ms for compact construction and1111ms for static
construction including printing each list of sizes. Static filtering adds setup
work and reduces the candidate domains. This does not establish a whole-search
speedup or reject this pair. The separate StaticColumnPruning theorem proves that
every actual admissible column survives.

From `proofs`, run `lake env lean
../research/problems/erdos-85-wip-01/static_column_diagnostic/Benchmark.lean`.
