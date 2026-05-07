# Current State

**Phase**: ACT
**Since**: 2026-05-08T00:00:00.000Z
**Iteration**: 2

## Current Focus

Phase-2 ACTION COMPLETE. Created `Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean`
(221 lines, 1 new axiom, 8 theorems, 1 def, 0 sorries). Build verified
via Docker. Created gallery entry `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/`.

## Active Approach

Conjecture-isolation: package the open question as a single named axiom
`symBUDim_eq_largest_prime`, prove the lower-bound direction unconditionally
via parent infrastructure, derive the tight floor formula
`symBUDim n (2k) = 2k − 1` from the axiom + the cyclic-prime Yang-Borsuk
axiom inherited from the gallery. Verify consistency at n = 2.

## Blockers

None. Further progress requires either:
- Equivariant cohomology infrastructure in Mathlib (Fadell-Husseini index)
- An explicit equivariant construction proving the upper bound
- A counterexample at small composite n (n = 4, 6, 8 ...)

## Next Action

Phase-3 (optional): pedagogical annotations. Core proof scaffolding is complete.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
