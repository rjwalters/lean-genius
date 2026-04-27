# Current State

**Phase**: ACT
**Since**: 2026-03-28T15:00:00Z
**Iteration**: 4

## Current Focus

Open question OQ-01 asks: is the partition threshold of $\omega^{\omega^2}$
exactly 3 or 4? The Lean formalization in `proofs/Proofs/Erdos118Problem.lean`
proves the bracket result (theorem `omega_omega2_threshold`):

$$3 \leq \mathrm{partitionThreshold}(\omega^{\omega^2}) \leq 4$$

derived from:
- `counter_partition_3` axiom (Schipperus 1999/2010): $\omega^{\omega^2} \to (\omega^{\omega^2}, 3)^2$
- `counter_not_partition_5` axiom (Larson): $\omega^{\omega^2} \nrightarrow (\omega^{\omega^2}, 5)^2$
- `partition_monotone_down` theorem (proved, no axiom)

OQ-01 itself — pinning down whether the threshold is exactly 3 or exactly 4
— requires either proving `IsPartitionOrd counterexampleOrd 4` (then the
threshold is 4) or `¬ IsPartitionOrd counterexampleOrd 4` (then the
threshold is 3). Neither is currently in the literature.

## Active Approach

None — the bracket [3, 4] is the best known. Resolving OQ-01 to a single
value is a deep ordinal partition relation question and is the actual open
content of this slug.

## Blockers

- Need a settled answer to: does $\omega^{\omega^2} \to (\omega^{\omega^2}, 4)^2$ hold?
- The two `counter_*` axioms are themselves deep theorems from Schipperus/Larson;
  the analogous result at K_4 is, to my knowledge, still open.

## Next Action

This slug is a candidate to remain ACT (open) until either:
1. A literature result settles the K_4 case, after which a new axiom
   `counter_partition_4` or `counter_not_partition_4` can be added and
   `omega_omega2_threshold` strengthened to equality.
2. We deliberately mark BLOCKED on the upstream open problem.

The wider work referenced in JSON `knowledge.builtItems` (Erdos1182, etc.)
belongs to sibling slugs (erdos-1182-related). The OQ-01-specific deliverable
is the bracket theorem already in `Erdos118Problem.lean`, plus an honest
acknowledgement that the precise value is open.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (bracket [3, 4] via monotonicity)
- Approaches tried: 1
