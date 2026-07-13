# Current State

**Phase**: ORIENT
**Since**: 2026-07-03
**Iteration**: 2

## Current Focus

Closing the sole open obligation of `Proofs/BallotProblemOQ04OQ02OQ01.lean`:
`nonempty_firstReturnEquiv` — the first-return bijection realising the Catalan convolution
recurrence for non-crossing partitions of `Fin (n+1)`.

## Active Approach

Structural first-return decomposition (see knowledge.md §Decomposition strategy). The counting
half (`nonCrossingCount_recurrence_of_equiv`) is already proved; only the bijection remains.

## Blockers

- Mathlib has **no** non-crossing partition theory and **no** machinery for restricting a
  `Finpartition (Fin (n+1))` to a sub-interval. The restriction/gluing maps must be built from
  scratch (est. several hundred lines).
- Aristotle proof-search service returned `Resource not found` this session (unavailable); it is
  the natural async target for this HARD, *known*-mathematics bijection once reachable.

## Next Action

Build the restriction map `restrict : {P // IsNonCrossingFp P} (Fin (n+1)) → Finpartition (Fin i)`
for the interval cut out by the block of a distinguished point, and prove it preserves
`IsNonCrossingFp`. See knowledge.md for the full sub-lemma breakdown.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (brute-force finite verification at n=4 — rejected, see knowledge.md)
