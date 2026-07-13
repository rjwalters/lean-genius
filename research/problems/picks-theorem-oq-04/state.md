# Research State: picks-theorem-oq-04

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-28
**Iteration**: 2

## Current Focus
SOLVED. General n-gon shoelace formula + integrality bridge formalized and
verified in `proofs/Proofs/PicksTheoremOQ04.lean` (0 sorries, 0 axioms,
no native_decide). Gallery data added.

## Active Approach
Fan-triangulation reduction: model the polygon as a `List (ℤ × ℤ)`, define the
closed shoelace sum and the fan sum, and prove they are equal
(`shoelace_eq_fan`) via the apex-decomposition identity
`cross2 o a b = cross a b + cross b o - cross a o`. This lifts the gallery's
triangle shoelace formula to arbitrary n, and the integrality bridge to Pick
(`pick_bridge` / `pick_bridge_iff`) follows because the shoelace sum is an integer.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None.

## Next Action
Done. Follow-up directions recorded in meta openQuestions: (1) constructive Pick
via Lean ear/fan triangulation to remove the realizability hypothesis;
(2) orientation (reversal) and cyclic-rotation invariance of the shoelace sum.
