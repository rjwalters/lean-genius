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
- [x] `key_inequality_trig_core` — geometry-free trig bound, PROVED.
- [x] `key_inequality_of_chord_and_sines` — verified assembly: from the chord
  identity + law of sines, derives the key inequality `b·dc + c·db ≤ a·PA`, PROVED.
- [ ] `key_inequality_*` — the three geometric key inequalities (OPEN / hard);
  each now reduces to supplying the chord identity and the law of sines for the
  concrete Euclidean configuration (see `key_inequality_of_chord_and_sines`).
- [ ] `erdos_mordell` — assembled geometric statement (depends on the above).

The reduction, the trig core, and the chord-to-key assembly are the reusable,
Mathlib-independent heart of the argument; the remaining work is purely the
planar-geometry derivation of the chord identity and law of sines (deferred —
see knowledge notes).

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

/-- **Trigonometric core of the key inequality** (geometry-free).

For triangle angles `A, B, C` (so `A + B + C = π`) with `sin B, sin C ≥ 0`, and
nonnegative pedal distances `db, dc`,
    `sin B · dc + sin C · db ≤ √(db² + dc² + 2·db·dc·cos A)`.

The right-hand side is exactly `PA · sin A` once the geometric *chord identity*
`(PA · sin A)² = db² + dc² + 2·db·dc·cos A` (concyclicity of the pedal feet on
the circle of diameter `PA`) is established; combined with the law of sines
`a = 2R sin A`, `b = 2R sin B`, `c = 2R sin C`, this lemma yields the key
inequality `a·PA ≥ b·dc + c·db`.

The whole estimate collapses to the perfect square `(db·cos C − dc·cos B)² ≥ 0`
after substituting `cos A = sin B sin C − cos B cos C` (valid since `A = π−B−C`).
This isolates the *single* remaining geometric obligation (the chord identity);
everything trigonometric is proved here. -/
theorem key_inequality_trig_core
    {A B C db dc : ℝ}
    (hsum : A + B + C = Real.pi)
    (hdb : 0 ≤ db) (hdc : 0 ≤ dc)
    (hsB : 0 ≤ Real.sin B) (hsC : 0 ≤ Real.sin C) :
    Real.sin B * dc + Real.sin C * db
      ≤ Real.sqrt (db ^ 2 + dc ^ 2 + 2 * db * dc * Real.cos A) := by
  -- The angle-sum identity gives `cos A` in terms of `B, C`.
  have hcosA : Real.cos A = Real.sin B * Real.sin C - Real.cos B * Real.cos C := by
    have hA : A = Real.pi - (B + C) := by linarith
    rw [hA, Real.cos_pi_sub, Real.cos_add]; ring
  -- The left-hand side is nonnegative.
  have hLHS : 0 ≤ Real.sin B * dc + Real.sin C * db :=
    add_nonneg (mul_nonneg hsB hdc) (mul_nonneg hsC hdb)
  -- Squared comparison reduces to a perfect square via `sin² + cos² = 1`.
  have hsq : (Real.sin B * dc + Real.sin C * db) ^ 2
      ≤ db ^ 2 + dc ^ 2 + 2 * db * dc * Real.cos A := by
    rw [hcosA]
    nlinarith [sq_nonneg (db * Real.cos C - dc * Real.cos B),
               Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C,
               mul_nonneg hdb hdc]
  -- Take square roots.
  calc Real.sin B * dc + Real.sin C * db
      = Real.sqrt ((Real.sin B * dc + Real.sin C * db) ^ 2) := (Real.sqrt_sq hLHS).symm
    _ ≤ Real.sqrt (db ^ 2 + dc ^ 2 + 2 * db * dc * Real.cos A) := Real.sqrt_le_sqrt hsq

/-- **Key inequality from the chord identity and the law of sines** (geometry-free).

This is the verified *assembly* step: it takes the two geometric facts that the
chord identity provides and produces the Erdős–Mordell key inequality
`b · dc + c · db ≤ a · PA` purely algebraically, via `key_inequality_trig_core`.

The two inputs are exactly:
* the **chord identity** `hchord : (PA · sin A)² = db² + dc² + 2·db·dc·cos A`
  (concyclicity of the pedal feet on the circle of diameter `PA`), and
* the **law of sines** with a common circumradius `R > 0`:
  `a = 2R sin A`, `b = 2R sin B`, `c = 2R sin C`.

Together with the angle sum `A + B + C = π` and the obvious sign conditions, the
trig core gives `sin B · dc + sin C · db ≤ PA · sin A`; scaling by `2R > 0`
turns this into `b · dc + c · db ≤ a · PA`. After this lemma, the *only*
remaining geometric obligation in each `key_inequality_*` is to exhibit the
chord identity and the law of sines for the concrete Euclidean configuration. -/
theorem key_inequality_of_chord_and_sines
    {A B C a b c db dc PA R : ℝ}
    (hsum : A + B + C = Real.pi)
    (hsA : 0 ≤ Real.sin A) (hsB : 0 ≤ Real.sin B) (hsC : 0 ≤ Real.sin C)
    (hdb : 0 ≤ db) (hdc : 0 ≤ dc) (hPA : 0 ≤ PA) (hR : 0 < R)
    (haR : a = 2 * R * Real.sin A) (hbR : b = 2 * R * Real.sin B)
    (hcR : c = 2 * R * Real.sin C)
    (hchord : (PA * Real.sin A) ^ 2 = db ^ 2 + dc ^ 2 + 2 * db * dc * Real.cos A) :
    b * dc + c * db ≤ a * PA := by
  -- The trig core bounds the pedal projection by the chord √(…).
  have htrig := key_inequality_trig_core hsum hdb hdc hsB hsC
  -- The chord identity collapses √(…) to `PA · sin A` (nonnegative).
  have hchordNN : 0 ≤ PA * Real.sin A := mul_nonneg hPA hsA
  have hroot : Real.sqrt (db ^ 2 + dc ^ 2 + 2 * db * dc * Real.cos A) = PA * Real.sin A := by
    rw [← hchord, Real.sqrt_sq hchordNN]
  rw [hroot] at htrig
  -- htrig : sin B · dc + sin C · db ≤ PA · sin A.  Scale by `2R > 0`.
  have hscaled : 2 * R * (Real.sin B * dc + Real.sin C * db)
      ≤ 2 * R * (PA * Real.sin A) :=
    mul_le_mul_of_nonneg_left htrig (by linarith)
  -- Rewrite both sides into the side-length form.
  calc b * dc + c * db
      = 2 * R * (Real.sin B * dc + Real.sin C * db) := by rw [hbR, hcR]; ring
    _ ≤ 2 * R * (PA * Real.sin A) := hscaled
    _ = a * PA := by rw [haR]; ring

/-- Perpendicular distance from a point `P` to the line through two points
`X Y`, as the distance from `P` to the affine span `line[X, Y]`. -/
noncomputable def lineDist (P X Y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Metric.infDist P (affineSpan ℝ {X, Y})

/-- The pedal distances are nonnegative (immediate, `infDist ≥ 0`). -/
theorem lineDist_nonneg (P X Y : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ lineDist P X Y :=
  Metric.infDist_nonneg

/-- **Erdős–Mordell key inequality at vertex `A`.**

`a · PA ≥ b · dc + c · db`, with `a = BC`, `b = CA`, `c = AB`, `db = dist(P, CA)`,
`dc = dist(P, AB)`. Geometrically: the feet of the perpendiculars from `P` to the
two sides meeting at `A` are concyclic with `A` and `P` on a circle of diameter
`PA`; projecting the chord between the feet gives this bound.

This is the geometry-bearing obligation (OPEN / hard to formalize); the other two
are its cyclic images. -/
theorem key_inequality_A
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    dist C A * lineDist P A B + dist A B * lineDist P C A ≤ dist B C * dist P A := by
  sorry

/-- **Erdős–Mordell key inequality at vertex `B`** (cyclic image of `key_inequality_A`). -/
theorem key_inequality_B
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    dist A B * lineDist P B C + dist B C * lineDist P A B ≤ dist C A * dist P B := by
  sorry

/-- **Erdős–Mordell key inequality at vertex `C`** (cyclic image of `key_inequality_A`). -/
theorem key_inequality_C
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    dist B C * lineDist P C A + dist C A * lineDist P B C ≤ dist A B * dist P C := by
  sorry

/-- **Erdős–Mordell inequality** (geometric statement).

For `P` interior to a nondegenerate triangle `A B C` in the Euclidean plane,
the sum of distances to the vertices is at least twice the sum of distances to
the sides.

The proof is fully assembled: positivity of the side lengths (from affine
independence), nonnegativity of the pedal distances, and the AM–GM algebra are
all discharged here via `erdos_mordell_reduction`. The *only* remaining inputs
are the three geometric `key_inequality_*` lemmas. -/
theorem erdos_mordell
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    2 * (lineDist P B C + lineDist P C A + lineDist P A B)
      ≤ dist P A + dist P B + dist P C := by
  -- Vertices are pairwise distinct (affine independence ⟹ injective indexing).
  have hinj := hABC.injective
  have hBC : B ≠ C := by
    intro h
    have h12 : (1 : Fin 3) = 2 := hinj (by simpa using h)
    exact absurd h12 (by decide)
  have hCA : C ≠ A := by
    intro h
    have h20 : (2 : Fin 3) = 0 := hinj (by simpa using h)
    exact absurd h20 (by decide)
  have hAB : A ≠ B := by
    intro h
    have h01 : (0 : Fin 3) = 1 := hinj (by simpa using h)
    exact absurd h01 (by decide)
  -- Side lengths are strictly positive.
  have ha : 0 < dist B C := dist_pos.mpr hBC
  have hb : 0 < dist C A := dist_pos.mpr hCA
  have hc : 0 < dist A B := dist_pos.mpr hAB
  -- Assemble via the algebraic reduction.
  exact erdos_mordell_reduction ha hb hc
    (lineDist_nonneg P B C) (lineDist_nonneg P C A) (lineDist_nonneg P A B)
    (key_inequality_A A B C P hABC hP)
    (key_inequality_B A B C P hABC hP)
    (key_inequality_C A B C P hABC hP)

end ErdosMordellOQ01
