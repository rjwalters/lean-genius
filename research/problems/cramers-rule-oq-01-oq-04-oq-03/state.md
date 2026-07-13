# Current State

**Phase**: DESIGN
**Since**: 2026-07-01
**Iteration**: 1

## Current Focus
Faddeev–LeVerrier as a computable Lean function extending CramersRuleOQ01OQ04.lean.

## Findings (researcher-6, 2026-07-01)
- Mathlib has NO Faddeev–LeVerrier; genuine gap. Charpoly/trace/Cayley–Hamilton pieces exist.
- Parent file (namespace CramersRuleNewton) already has matPowerSum, charpolyCoeff,
  cayley_hamilton, and an axiom `faddeev_leverrier_inversion` that an FL recurrence would discharge.
- KEY CONSTRAINT: the FL recurrence divides by k ⇒ cannot extend over the parent's plain
  [CommRing R]; needs [Field R][CharZero R] / [Invertible (k:R)], or a division-free scaled
  reformulation (k • cₖ = -tr(A Mₖ), matching the seeder's "k·Mₖ" phrasing).
- Concrete Lean structuring + correctness plan in knowledge.md (pair-valued recursion).

## Active Approach
Author `flStep` (pair-valued recursion) over a char-0 field + prove `flCoeff = charpolyCoeff`.

## Blockers
- Build blocked all session: concurrent lean-build containers share the .lake cache volume
  (SIGBUS). Build only when `docker ps | grep lean-build` is empty. No compile performed.

## Next Action
1. Write `flStep` + `flCoeff = charpolyCoeff` correctness over [Field R][CharZero R].
2. #eval a Matrix (Fin 3) ℚ example; discharge parent's faddeev_leverrier_inversion axiom.

## Attempt Counts
- Total attempts: 1 (design/survey; no build)
- Approaches tried: API survey + algorithm/ring-constraint analysis
