# British Flag Theorem (british-flag-theorem-oq-01)

## Problem
For a rectangle `ABCD` and **any** point `P`, `PA² + PC² = PB² + PD²` (the sums
of squared distances to opposite corners are equal).

## Status: COMPLETED (build-verified, 0 sorries, 0 axioms)

## Core Insight
Writing the rectangle through edge vectors `u = B - A`, `v = D - A` (so
`C = A + u + v`), the difference of the two squared-distance sums is

  (PA² + PC²) − (PB² + PD²) = 2⟨u, v⟩,

**independent of P**. The theorem is therefore equivalent to `⟨u, v⟩ = 0`, i.e.
to `ABCD` being a rectangle rather than a general parallelogram. The right angle
is the entire mathematical content.

## Formalization (`proofs/Proofs/BritishFlagTheorem.lean`)
1. `british_flag_coords` — real-coordinate identity. Both sides are real
   polynomials whose difference is `2(ux*vx + uy*vy)`; closed by
   `linear_combination 2 * hperp`.
2. `british_flag` — complex / metric-distance form. Rectangle encoded by
   `C = B + D - A` and `(B-A).re*(D-A).re + (B-A).im*(D-A).im = 0`. Each
   `dist · · ^ 2` is rewritten to coordinates via the helper
   `dist z w ^ 2 = (z.re-w.re)^2 + (z.im-w.im)^2` (from `Complex.dist_eq_re_im`
   and `Real.sq_sqrt`), then reduced to `british_flag_coords`.
3. `british_flag_needs_right_angle` — sharpness: `u = (2,0)`, `v = (1,1)` give
   `⟨u,v⟩ = 2 ≠ 0` and `PA²+PC² = 10 ≠ 6 = PB²+PD²`. Defect `2⟨u,v⟩ = 4`.

## Mathlib Notes
- `Complex.sq_abs` does **not** exist in Mathlib v4.26.0 (build attempt 1 failed
  on `Unknown constant 'Complex.sq_abs'`). Use `Complex.dist_eq_re_im` +
  `Real.sq_sqrt` to convert a squared complex distance to coordinates instead.

## Follow-up Open Questions
- Higher-dimensional version in `EuclideanSpace ℝ (Fin n)` (the coordinate proof
  is dimension-agnostic — only bilinearity + the right angle are used).
- Converse: if `PA²+PC² = PB²+PD²` for all `P`, must the parallelogram be a
  rectangle? (The `2⟨u,v⟩` analysis says yes.)
