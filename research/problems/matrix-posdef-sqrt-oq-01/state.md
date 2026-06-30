# Current State

**Phase**: COMPLETED
**Since**: 2026-06-20
**Iteration**: 1

## Current Focus

Verified 0-axiom gallery entry shipped: `proofs/Proofs/MatrixPosDefSqrtOQ01.lean`.

## Active Approach

Package the positive semidefinite square root `CFC.sqrt` (modern Mathlib; the
bespoke `Matrix.PosSemidef.sqrt` was deprecated 2025-09-22) as a triad —
existence/defining property, structure (PSD/Hermitian), uniqueness — and read
the corollaries (√0 = 0, √1 = 1, √(A²) = A), the determinant shadow
det(√A)² = det A, and the concrete instance √diag(4,9) = diag(2,3) off uniqueness.

## Blockers

None.

## Next Action

Follow-ups: polar decomposition A = P·U with P = √(AᴴA); operator absolute value
|A| = √(AᴴA); Loewner monotonicity 0 ⪯ A ⪯ B ⟹ √A ⪯ √B.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
