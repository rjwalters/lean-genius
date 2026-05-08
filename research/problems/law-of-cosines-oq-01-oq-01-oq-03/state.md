# Current State

**Phase**: AXIOM_REDUCTION
**Since**: 2026-05-08T01:30:00Z
**Iteration**: 4

## Current Focus

Eliminate the final remaining axiom `polar_angle_eq` to graduate the entry from
`status: axiomatized` (badge: `axiom`) to `status: verified`.

The proof of `polar_angle_eq` is the polar-triangle dual of the proved theorem
`polar_side_eq_pi_minus_angle`. It states that the dihedral angle at the polar
vertex `C' = normalize(A×B)` equals `π - arcLen A B`.

## Active Approach

Apply the same `cross_dot_eq_neg_projperp` algebraic core that works for the
side formula, but now to the *polar* triangle's `projPerp` expressions. The
key auxiliary identities are:

1. `(C×A) ×₃ (A×B) = tripleProduct A B C • A`
2. `(B×C) ×₃ (A×B) = tripleProduct A B C • B`
3. Non-degeneracy: `tripleProduct A B C ≠ 0` when `B×C, C×A, A×B` are all nonzero.
4. Sign analysis on `normalize3` of scalar-multiplied unit vectors.

After this reduction, `dot(projPerp(B×C, A×B), projPerp(C×A, A×B)) = -dot(A,B)`
(possibly up to sign from `sign(tripleProduct)`), reducing to the side formula
applied symmetrically.

## Blockers

None mathematical. Implementation cost ≈ 80–100 lines of Lean 4 against current
Mathlib, with one Docker rebuild cycle per syntactic-error fix.

## Next Action

Open a `research/...` branch, add the three cross-cross identities as helper
lemmas, then prove `polar_angle_eq` (replacing the `axiom` declaration with a
`theorem ... := by ...`). Verify with `./proofs/scripts/docker-build.sh
Proofs.LawOfCosinesOQ01OQ01OQ03`.

## Attempt Counts

- Total attempts: 3 (all merged)
- Current approach attempts: 0 (axiom-elimination of `polar_angle_eq` not yet attempted)
- Approaches tried: 3 — see knowledge.md sessions 1, 2, 3
