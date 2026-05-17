# Current State

**Phase**: COMPLETED
**Since**: 2026-03-24T15:15:41Z (registry graduated)
**Iteration**: 5

## Deliverable (Shipped)

The deliverable for this slug is the bracket result for
$\mathrm{partitionThreshold}(\omega^{\omega^2})$, formalized in
`proofs/Proofs/Erdos118Problem.lean` (139 lines, 2 axioms, 0 sorries):

$$3 \leq \mathrm{partitionThreshold}(\omega^{\omega^2}) \leq 4$$

theorem `omega_omega2_threshold`, derived via:

- `counter_partition_3` axiom (Schipperus 1999/2010, Darby 1999):
  $\omega^{\omega^2} \to (\omega^{\omega^2}, 3)^2$
- `counter_not_partition_5` axiom (Larson):
  $\omega^{\omega^2} \nrightarrow (\omega^{\omega^2}, 5)^2$
- `partition_monotone_down` (proved, no axiom)
- `partition_monotone_up_neg` (proved, no axiom)
- `partition_transition_exists` (proved by strong induction, no axiom — added
  in PR #16227 to eliminate the two previously-axiomatized definitional
  axioms `partitionThreshold` and `threshold_exact`)

Axiom count history: original 4 → 2 (PR #16227 eliminated the two
definitional axioms).

## Residual Open Mathematics

OQ-01 itself — pinning down whether the threshold is exactly 3 or
exactly 4 — requires either proving `IsPartitionOrd counterexampleOrd 4`
(then the threshold is 4) or `¬ IsPartitionOrd counterexampleOrd 4`
(then the threshold is 3). To my knowledge, neither is currently
settled in the literature: the analogous result at $K_4$ is open.
This is upstream open mathematics, not a Lean-formalization gap, and
is consequently not actionable from this slug.

## Re-Open Trigger

If a literature result settles the $K_4$ case, this slug can be
re-opened to:

1. Add a new axiom `counter_partition_4` or `counter_not_partition_4`.
2. Strengthen `omega_omega2_threshold` to equality.

Until then, the bracket [3, 4] is the best known and is the final
deliverable.

## Cross-References

- Gallery: `src/data/proofs/erdos-118/` (canonical: 2 axioms, 139 lines,
  6 theorems, 4 definitions, 0 sorries, status `axiomatized`, badge `axiom`)
- Lean: `proofs/Proofs/Erdos118Problem.lean`
- Predecessors: PR #1280 (initial formalization), PR #5873 (axiom-elim
  survey), PR #5911 (`omega_omega2_threshold` + threshold guard), PR #7445
  (`ordPartition` definition + `partition_monotone_down`), PR #16227
  (4→2 axiom reduction via `partition_transition_exists`).
- Related: Erdős #592 (`relation_to_592` documents the connection).

## Attempt Counts

- Total attempts: 5 (4 prior research arcs + this STATE-SYNC catchup)
- Approaches tried: 1 (bracket [3, 4] via monotonicity + transition)
