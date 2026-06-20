# Knowledge Base: menelaus-theorem-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Menelaus's theorem (transversal companion of Ceva): for triangle ABC and points
X on BC, Y on CA, Z on AB, the points X,Y,Z are collinear iff the product of
signed side ratios (BX/XC)·(CY/YA)·(AZ/ZB) = -1. Not a named Mathlib result.

Parametrisation used: X=(1-t)B+tC, Y=(1-u)C+uA, Z=(1-v)A+vB, so the signed
ratios are t/(1-t), u/(1-u), v/(1-v).

---

## Insights

- **Determinant factorisation is the whole content.** Encode collinearity in ℝ²
  by the signed-area determinant collinearDet P Q R = (Q.1-P.1)(R.2-P.2) -
  (Q.2-P.2)(R.1-P.1). Then, exactly:
      collinearDet X Y Z = (t·u·v + (1-t)(1-u)(1-v)) · collinearDet A B C.
  Verified symbolically in sympy first; in Lean it is a one-line `ring`.
- The scalar factor `t·u·v + (1-t)(1-u)(1-v)` expands to
  `1 - t - u - v + tu + tv + uv` (the tuv terms cancel) — equivalently the
  Menelaus condition tuv = -(1-t)(1-u)(1-v).
- Non-degeneracy of the triangle (collinearDet A B C ≠ 0) is precisely what lets
  `mul_eq_zero` + `or_iff_left` cancel the area factor and isolate the scalar.
- Matching the scalar condition to the product form is `div_mul_div_comm` (×2) +
  `div_eq_iff` + `linear_combination`. Only parameters ≠ 1 are needed (no t≠0).
- Mirrors Ceva: same affine-parameter / signed-ratio framework, product +1
  (concurrency) vs -1 (collinearity).

---

## Dead Ends

- None. The first approach (signed-area determinant + ring factorisation) worked
  cleanly. No EuclideanSpace / AffineMap machinery was needed — plain ℝ×ℝ with
  coordinate projections keeps `ring` happy.

---

## Session Log

### 2026-06-16 (s01) — FRESH, COMPLETED
- **Outcome**: completed (pending green build + merge).
- Wrote `proofs/Proofs/MenelausTheorem.lean` (139 lines, 0 sorry, 0 axiom):
  `collinearDet`, `Collinear3`, `MenelausConfig`, `ptX/ptY/ptZ`,
  `menelausProduct`, `collinearDet_factor`, main `menelaus`, two directional
  corollaries, and a concrete numeric instance (t=u=2, v=-1/3 → product -1).
- Authored gallery data: `src/data/proofs/menelaus-theorem-oq-01/{meta,annotations}.json`.
- Built by module name via docker-build (`.lake` self-symlink forced a Mathlib
  re-clone in-container).
- **Next**: register in Proofs.lean (after MeanValueTheoremOQ04), open `research` PR.
