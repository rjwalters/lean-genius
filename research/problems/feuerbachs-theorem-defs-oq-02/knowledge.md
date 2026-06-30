# Knowledge Base: feuerbachs-theorem-defs-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Resolution (2026-06-25, researcher-1)

**SOLVED** — shipped as gallery slug `feuerbachs-theorem-defs-oq-05`
(`Proofs/FeuerbachsTheoremDefsOQ05.lean`), PR #29810. The candidate slug
`feuerbachs-theorem-defs-oq-02` was already occupied in the gallery by Euler's
triangle formula (OI² = R² − 2Rr), so the nine-point-uniqueness deliverable this
candidate describes was minted under the next free top-level slug oq-05.

### Proof architecture (verified, 0 axioms, 0 sorries)
- `equidistant_center_unique`: two points equidistant (squared distance) from
  three non-collinear points coincide. Subtracting the squared-distance equations
  cancels quadratics → 2×2 linear system; its determinant is the orientation
  determinant of the three points; Cramer via `linear_combination`.
- `midpoints_noncollinear`: side-midpoint orientation determinant = (1/4) × the
  triangle's non-degeneracy determinant (since M_b−M_a=(A−B)/2, M_c−M_a=(A−C)/2).
- `ninePointCircle_unique`: any circle through the 3 side midpoints is the
  nine-point circle (centre N, radius R/2). Only 3 of the 9 points are needed.

### Key facts
- Worked entirely in the parent's coordinate API (Point=ℝ×ℝ, dist2, dist2_sq).
- `dist2_sq Q P = (dist2 Q P)^2` (Real.sq_sqrt) bridges parent's sqrt membership
  to the polynomial linear system.
- Mathlib's abstract circumcircle uniqueness was NOT used — a self-contained
  coordinate proof was cleaner and matches the parent framework.
