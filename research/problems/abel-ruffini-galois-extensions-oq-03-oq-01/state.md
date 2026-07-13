# Research State: abel-ruffini-galois-extensions-oq-03-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-03T21:15:00-07:00
**Iteration**: 3

## Current Focus
SOLVED. `isSimpleGroup_alternating` (in
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ03OQ01.lean`) is a complete,
machine-checked proof of unconditional simplicity of `Aₙ` for every finite `α`
with `5 ≤ card α`, generalizing Mathlib's `Fin 5`-only `isSimpleGroup_five`.
0 sorry, 0 axiom (`#print axioms` → `propext, Classical.choice, Quot.sound`).

## Active Approach
Jordan minimal-support / commutator argument, fully formalized:
- Two strict-support-decrease engines: `exists_smaller_commutator_of_five_points`
  (Case A, cycle of length ≥3) and `exists_smaller_commutator_of_involution`
  (Case B, product of disjoint transpositions).
- Crux `isThreeCycle_of_min_support`: `by_cases σ²=1` → Case B; else Case A with
  sub-split `#support ≥ 5` (engine A) vs `#support = 4` (σ is a 4-cycle, odd via
  `IsCycle.sign`, contradiction).

## Attempt Count
- Total attempts: 4 sessions
- Approaches tried: 1 (minimal-support/commutator — succeeded)

## Blockers
None. (Aristotle MCP was down all sessions; the proof was completed by hand.)

## Next Action
Promote to a verified gallery entry (Seeker/Enricher) and prepare a candidate
Mathlib PR: general `alternatingGroup.isSimpleGroup` for `5 ≤ card α`.
