# Bounded Lean column-prefix diagnostic

Both runs use full U compact parameters (6,6,15), R representative14,
production static column domains, and production capacity, external-cap and
C4 predicates. An instrumented IO traversal stops after5000 attempted prefixes;
it checks exact degrees at complete leaves. Joint-family acceptance is disabled.
This instrumented traversal has no proved equality with the production DFS.

Compact candidate order: setup1197ms, traversal3703ms,4105capacity rejections,
567C4 rejections,0external-cap rejections,0leaves.
Lexicographic combination order: setup1197ms, traversal3124ms,4243capacity
rejections,417C4 rejections,0external-cap rejections,8leaves.
Neither search exhausted. Both process runs exited0 within30s deadlines.
Clock intervals include the corresponding printed output.

The second order sorts each equal-cardinality column domain by descending sum
of 2^(14-i) over its members, matching lexicographic combinations of U labels.
The eight leaves agree with the earlier Python prefix diagnostic. Rejection
categories differ because Python also counts the near-row cap as capacity,
whereas here the production C4 predicate handles that root constraint.
This shows sensitivity of bounded prefixes to ordering, not a general search
speedup, rejection certificate, or completed U/R-pair search.

From proofs, run `lake env lean --run ../research/problems/erdos-85-wip-01/lean_column_prefix_diagnostic/Compact.lean`
or substitute `Lexicographic.lean`. Logs and run receipts retain observed times;
repeat timings may vary. No source check by evaluation is used as a proof.
