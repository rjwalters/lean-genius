/-
# Erdős–Mordell Inequality (OQ-01): Formalization and Algebraic Core

## Statement

For a point `P` in the interior of triangle `ABC`, let `da, db, dc` be the
perpendicular distances from `P` to the sides `BC, CA, AB` respectively.
Then
                PA + PB + PC ≥ 2 (da + db + dc),
with equality iff `ABC` is equilateral and `P` is its center.

This is the classical Erdős–Mordell inequality (conjectured by Erdős 1935,
first proved by Mordell and Barrow 1937). It is **not** currently in Mathlib.

## Proof architecture

The standard proof factors into two independent pieces:

1. **Geometric key inequalities** (the hard, geometry-bearing step).
   Writing `a = BC`, `b = CA`, `c = AB` for the side lengths, one shows the
   three cyclic inequalities
        a · PA ≥ b · dc + c · db,
        b · PB ≥ c · da + a · dc,
        c · PC ≥ a · db + b · da.
   Each follows from the cyclic-quadrilateral / projection argument: the feet
   of the perpendiculars from `P` to the two sides at a vertex are concyclic
   with `P` and that vertex on a circle of diameter equal to the vertex
   distance, and projecting onto the chord gives the bound.

2. **Algebraic reduction** (this file, fully proved). Dividing the three key
   inequalities by `a, b, c` and summing, the coefficient of each `d` is a sum
   `t + 1/t ≥ 2` (AM–GM), giving the Erdős–Mordell bound. Concretely the
   certificate is the algebraic identity
        a·b·c·(PA+PB+PC) − 2·a·b·c·(da+db+dc)
          = a·da·(b−c)² + b·db·(a−c)² + c·dc·(a−b)² + (key-inequality slack),
   each summand of which is nonnegative.

## Status

- [x] `erdos_mordell_reduction` — the AM–GM reduction (algebraic core), PROVED.
- [ ] `key_inequality_*` — the three geometric key inequalities (OPEN / hard).
- [ ] `erdos_mordell` — assembled geometric statement (depends on the above).

The reduction is the reusable, Mathlib-independent heart of the argument; the
remaining work is purely the planar-geometry derivation of the key
inequalities (deferred — see knowledge notes).

## References
- P. Erdős, *Problem 3740*, Amer. Math. Monthly 42 (1935), 396.
- L. J. Mordell & D. F. Barrow, *Solution to 3740*, Amer. Math. Monthly 44 (1937), 252–254.
- A. Avez, *A short proof of the Erdős–Mordell theorem*, Amer. Math. Monthly 100 (1993).
-/

import Mathlib

namespace ErdosMordellOQ01

/-- **Erdős–Mordell algebraic reduction.**

Given the three Erdős–Mordell *key inequalities* relating the vertex distances
`PA, PB, PC` to the pedal distances `da, db, dc` (weighted by the side lengths
`a, b, c`), the Erdős–Mordell inequality `PA + PB + PC ≥ 2(da + db + dc)`
follows purely algebraically via AM–GM.

This is the side-length/AM–GM core; it carries no geometric hypotheses and is
reusable for any proof that establishes the key inequalities. -/
theorem erdos_mordell_reduction
    {a b c da db dc PA PB PC : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hda : 0 ≤ da) (hdb : 0 ≤ db) (hdc : 0 ≤ dc)
    (h1 : b * dc + c * db ≤ a * PA)
    (h2 : c * da + a * dc ≤ b * PB)
    (h3 : a * db + b * da ≤ c * PC) :
    2 * (da + db + dc) ≤ PA + PB + PC := by
  -- Scale each key inequality by the product of the two *other* side lengths,
  -- clearing denominators to land on the common factor `a*b*c`.
  have e1 : b * c * (b * dc + c * db) ≤ b * c * (a * PA) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hb.le hc.le)
  have e2 : a * c * (c * da + a * dc) ≤ a * c * (b * PB) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg ha.le hc.le)
  have e3 : a * b * (a * db + b * da) ≤ a * b * (c * PC) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg ha.le hb.le)
  -- AM–GM slack terms: `x·d·(y−z)² ≥ 0`.
  have s1 : 0 ≤ a * da * (b - c) ^ 2 :=
    mul_nonneg (mul_nonneg ha.le hda) (sq_nonneg _)
  have s2 : 0 ≤ b * db * (a - c) ^ 2 :=
    mul_nonneg (mul_nonneg hb.le hdb) (sq_nonneg _)
  have s3 : 0 ≤ c * dc * (a - b) ^ 2 :=
    mul_nonneg (mul_nonneg hc.le hdc) (sq_nonneg _)
  have habc : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  -- The exact nonnegative certificate: summing the six facts above yields
  --   a·b·c·(PA+PB+PC) − a·b·c·(2(da+db+dc)) = e-slack + s1 + s2 + s3 ≥ 0.
  have key : a * b * c * (2 * (da + db + dc)) ≤ a * b * c * (PA + PB + PC) := by
    nlinarith [e1, e2, e3, s1, s2, s3]
  exact le_of_mul_le_mul_left key habc

/-- Perpendicular distance from a point `P` to the line through two points
`X Y`, as the distance from `P` to the affine span `line[X, Y]`. -/
noncomputable def lineDist (P X Y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Metric.infDist P (affineSpan ℝ {X, Y})

/-- The pedal distances are nonnegative (immediate, `infDist ≥ 0`). -/
theorem lineDist_nonneg (P X Y : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ lineDist P X Y :=
  Metric.infDist_nonneg

/-- **Erdős–Mordell inequality** (geometric statement).

For `P` interior to a nondegenerate triangle `A B C` in the Euclidean plane,
the sum of distances to the vertices is at least twice the sum of distances to
the sides.

The proof is `erdos_mordell_reduction` applied to the three geometric key
inequalities; those key inequalities are the remaining open obligation. -/
theorem erdos_mordell
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    2 * (lineDist P B C + lineDist P C A + lineDist P A B)
      ≤ dist P A + dist P B + dist P C := by
  sorry

end ErdosMordellOQ01
