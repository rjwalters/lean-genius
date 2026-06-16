# Knowledge: carnot-theorem-oq-01

## Problem Summary
Carnot's theorem: for a triangle with circumradius R and inradius r, the signed
distances from the circumcenter O to the three sides sum to R + r; equivalently
`cos A + cos B + cos C = 1 + r/R`. The analytic core (using Euler's inradius
formula `r/R = 4 sin(A/2) sin(B/2) sin(C/2)`) is the trigonometric identity

  `cos A + cos B + cos C = 1 + 4 sin(A/2) sin(B/2) sin(C/2)`,  for `A + B + C = π`.

## Status
**COMPLETED** (angle form) — `Proofs/CarnotTheorem.lean`, 0 axioms, 0 sorries, build-verified.

## Session 2026-06-16 (Session 1) — Carnot angle form

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Formalized the angle form of Carnot's theorem as a pure trigonometric identity
  over reals with `A + B + C = π` (no circumcenter / EuclideanSpace machinery).
- Proved the companion fundamental cosine identity
  `cos²A + cos²B + cos²C + 2 cos A cos B cos C = 1`.
- Registered in `proofs/Proofs.lean`; added gallery entry
  `src/data/proofs/carnot-theorem-oq-01/meta.json`.

### Key Findings / Technique
- **Half-angle linearization**: set `a=A/2, b=B/2, c=C/2`, so `a+b+c=π/2` and
  `c = π/2 - (a+b)`. Then `sin(C/2) = sin(π/2-(a+b)) = cos(a+b) = ca·cb - sa·sb`,
  removing the third angle.
- Rewrite each full cosine via `cos(2x) = 1 - 2 sin²x` (derived from Mathlib's
  `Real.cos_two_mul'` + `Real.cos_sq_add_sin_sq`).
- The goal then becomes a polynomial identity in `sin(A/2),cos(A/2),sin(B/2),cos(B/2)`
  closed by a single `linear_combination` of the two Pythagorean identities.
  Coefficients (sympy-verified):
    `(-2·cos(B/2)²)·pyth(A/2) + (2·(sin(A/2)²-1))·pyth(B/2)`.
- Companion identity: `cos C = -cos(A+B)` via `Real.cos_pi_sub`+`Real.cos_add`,
  then `linear_combination (1-cos²B)·pyth(A) + sin²A·pyth(B)`.

### Files Modified
- `proofs/Proofs/CarnotTheorem.lean` (new, 81 lines)
- `proofs/Proofs.lean` (import line)
- `src/data/proofs/carnot-theorem-oq-01/meta.json` (new)

### Next Steps (follow-ups, optional)
- Formalize the signed-distance form directly over `EuclideanSpace ℝ (Fin 2)`
  with an explicit circumcenter; needs Euler's inradius formula
  `r = 4R sin(A/2) sin(B/2) sin(C/2)` to bridge to the angle form.
