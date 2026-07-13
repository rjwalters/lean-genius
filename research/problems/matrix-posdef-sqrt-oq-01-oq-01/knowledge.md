# matrix-posdef-sqrt-oq-01-oq-01 — Polar decomposition from the PSD square root

**Status**: COMPLETED (0-axiom verified, PR #33089)

Answers open question 1 of parent `matrix-posdef-sqrt-oq-01`: formalize the
polar decomposition `A = U·P` with `P = √(AᴴA)` PSD, `U` unitary.

## Session 2026-07-02 (Session 1) — FRESH — COMPLETED

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Built `Proofs/MatrixPosDefSqrtOQ01OQ01.lean` (7 thm / 1 def / 183 L) on top of
  Mathlib `CFC.sqrt`, over `RCLike 𝕜`.
- Created gallery entry `src/data/proofs/matrix-posdef-sqrt-oq-01-oq-01/`.

### Key Findings
- **Uniqueness of the PSD factor needs no invertibility**: `A = U·P` (U unitary,
  P PSD) ⟹ `AᴴA = Pᴴ(UᴴU)P = P²` ⟹ `P = √(AᴴA)` by `CFC.sqrt_unique`. The
  modulus `|A| = √(AᴴA)` is intrinsic; only the unitary phase can be ambiguous.
- Invertibility transfers to the polar factor via determinant:
  `det(√(AᴴA))² = det(AᴴA) = |det A|² ≠ 0`.
- `Matrix.mul_eq_one_comm` gives the second unitarity identity for free (square).
- `noncomm_ring` handles matrix-associativity bookkeeping in `P⁻¹(AᴴA)P⁻¹ = 1`.

### Mathlib gap
- No polar decomposition of matrices in v4.26.0; no `partialIsometry`. General
  singular-case existence (partial-isometry extension) not built — flagged as
  out of scope. Existence/full-uniqueness claimed for invertible `A` only.

### Files Modified
- `proofs/Proofs/MatrixPosDefSqrtOQ01OQ01.lean` (new)
- `src/data/proofs/matrix-posdef-sqrt-oq-01-oq-01/meta.json` (new)

### Next Steps
- Extend existence to singular `A` (partial-isometry extension).
- Parent oq-02: operator absolute value `|A| = √(AᴴA)`, `‖Ax‖ = ‖|A|x‖`.
