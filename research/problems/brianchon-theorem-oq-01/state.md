# Research State: brianchon-theorem-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-19
**Iteration**: 2

## Current Focus
Proof complete and machine-verified. Brianchon's theorem is formalized as the
projective dual of Pascal's theorem in `proofs/Proofs/BrianchonTheorem.lean`
(builds clean, 0 sorries).

## Active Approach
Pole–polar dualization of Pascal (Approach 1 from problem.md), realized in the
homogeneous ℝ³ coordinate model: the tangent line at a contact point P is the
polar C·P; each Brianchon diagonal equals the fixed linear map (det C • C)
applied to the corresponding Pascal point, via the cofactor cross-product
identity.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (pole–polar dualization — SUCCESS)

## Result
- `concurrent_brianchon_of_collinear_pascal`: axiom-free, sorry-free duality
  bridge (Pascal collinearity ⟹ Brianchon concurrency). `#print axioms` shows
  only propext / Classical.choice / Quot.sound.
- `brianchon_theorem`: unconditional statement; uses exactly one axiom,
  `conic_implies_pascal` (the same fact axiomatized by `pascals-hexagon`).
- Status: axiomatized (1 axiom, 0 sorries). Verified via docker-build.sh.

## Blockers
None. (Remaining open: eliminate the shared `conic_implies_pascal` axiom — a
Pascal-side problem, tracked under `pascals-hexagon`.)

## Next Action
Done. Follow-up open questions recorded in the gallery entry's `openQuestions`.
