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
- [x] `chord_identity` — the chord identity at vertex `A`, PROVED (by delegation to
  `ErdosMordellChord.chord_identity` in `Proofs/ErdosMordellChordIdentity.lean`,
  whose cosine-side core `chord_cos_eq` is a pure coordinate identity in
  `EuclideanSpace ℝ (Fin 2)`).
- [x] `key_inequality_*` — the three geometric key inequalities, PROVED; each
  reduces to the chord identity and the law of sines for the concrete Euclidean
  configuration (see `key_inequality_of_chord_and_sines`).
- [x] `erdos_mordell` — assembled geometric statement, PROVED.

The inequality is now fully machine-checked with no `sorry` and no axioms beyond
Lean/Mathlib's standard foundations. The reduction, the trig core, and the
chord-to-key assembly are the reusable, Mathlib-independent heart of the argument;
the chord identity itself is discharged by the coordinate proof in the companion
file `ErdosMordellChordIdentity.lean`.

## References
- P. Erdős, *Problem 3740*, Amer. Math. Monthly 42 (1935), 396.
- L. J. Mordell & D. F. Barrow, *Solution to 3740*, Amer. Math. Monthly 44 (1937), 252–254.
- A. Avez, *A short proof of the Erdős–Mordell theorem*, Amer. Math. Monthly 100 (1993).
-/

import Mathlib
import Proofs.ErdosMordellChordIdentity

namespace ErdosMordellOQ01

open EuclideanGeometry

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

/-- **Law-of-sines reduction of the vertex-`A` key inequality** (geometry → algebra).

Given *only* the **chord identity** at vertex `A`
  `(PA · sin A)² = db² + dc² + 2·db·dc·cos A`   (with `A = ∠ B A C`),
the Erdős–Mordell key inequality `b·dc + c·db ≤ a·PA` follows. This lemma
discharges every remaining piece of trigonometric/circumradius bookkeeping for
the concrete Euclidean configuration:
* the **law of sines** `a = 2R·sin A`, `b = 2R·sin B`, `c = 2R·sin C` is obtained
  from `Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius` with `R` the
  circumradius of `△ABC` (positive by `Affine.Simplex.circumradius_pos`);
* the **angle sum** `A + B + C = π` from `angle_add_angle_add_angle_eq_pi`;
* the **sine positivity** `sin A, sin B, sin C > 0` from `sin_pos_of_not_collinear`.
It then invokes the proved geometry-free `key_inequality_of_chord_and_sines`.

After this lemma the *only* geometric obligation is `chord_identity`. -/
theorem key_inequality_A_of_chord
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hchord : (dist P A * Real.sin (∠ B A C)) ^ 2
        = lineDist P C A ^ 2 + lineDist P A B ^ 2
          + 2 * lineDist P C A * lineDist P A B * Real.cos (∠ B A C)) :
    dist C A * lineDist P A B + dist A B * lineDist P C A ≤ dist B C * dist P A := by
  -- The triangle and its (positive) circumradius.
  set t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A, B, C], hABC⟩ with ht
  have hpts : t.points = ![A, B, C] := by rw [ht]
  have hRpos : 0 < t.circumradius := t.circumradius_pos
  -- Non-collinearity (in every ordering) from affine independence.
  have hnc : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineIndependent_iff_not_collinear_set.mp hABC
  have ncBAC : ¬ Collinear ℝ ({B, A, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have e : ({B, A, C} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]; exact hnc
  have ncCBA : ¬ Collinear ℝ ({C, B, A} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have e : ({C, B, A} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]; exact hnc
  have ncACB : ¬ Collinear ℝ ({A, C, B} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have e : ({A, C, B} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]; exact hnc
  -- Sines of the three angles are positive.
  have hsA : 0 < Real.sin (∠ B A C) := sin_pos_of_not_collinear ncBAC
  have hsB : 0 < Real.sin (∠ C B A) := sin_pos_of_not_collinear ncCBA
  have hsC : 0 < Real.sin (∠ A C B) := sin_pos_of_not_collinear ncACB
  -- Vertices distinct (needed for the angle-sum lemma).
  have hinj := hABC.injective
  have hAB : A ≠ B := by
    intro h
    have h01 : (0 : Fin 3) = 1 := hinj (by simpa using h)
    exact absurd h01 (by decide)
  -- Triangle angle sum.
  have hsum : ∠ B A C + ∠ C B A + ∠ A C B = Real.pi := by
    have h := angle_add_angle_add_angle_eq_pi (p₁ := B) (p₂ := A) C hAB
    linarith [h]
  -- Law of sines for each side / opposite angle.
  have hlaw_a : dist B C = 2 * t.circumradius * Real.sin (∠ B A C) := by
    have h := t.dist_div_sin_angle_eq_two_mul_circumradius
      (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
    rw [hpts] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    exact (div_eq_iff hsA.ne').mp h
  have hlaw_b : dist C A = 2 * t.circumradius * Real.sin (∠ C B A) := by
    have h := t.dist_div_sin_angle_eq_two_mul_circumradius
      (i₁ := 2) (i₂ := 1) (i₃ := 0) (by decide) (by decide) (by decide)
    rw [hpts] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    exact (div_eq_iff hsB.ne').mp h
  have hlaw_c : dist A B = 2 * t.circumradius * Real.sin (∠ A C B) := by
    have h := t.dist_div_sin_angle_eq_two_mul_circumradius
      (i₁ := 0) (i₂ := 2) (i₃ := 1) (by decide) (by decide) (by decide)
    rw [hpts] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    exact (div_eq_iff hsC.ne').mp h
  -- Assemble through the proved geometry-free lemma.
  exact key_inequality_of_chord_and_sines hsum hsA.le hsB.le hsC.le
    (lineDist_nonneg P C A) (lineDist_nonneg P A B) dist_nonneg hRpos
    hlaw_a hlaw_b hlaw_c hchord

/-- **Chord identity at vertex `A`** (PROVED — formerly the sole remaining geometric obligation).

Let `F_b, F_c` be the feet of the perpendiculars from `P` to the sides `CA, AB`,
so `db = dist P F_b = lineDist P C A` and `dc = dist P F_c = lineDist P A B`. The
points `A, F_b, F_c, P` are concyclic on the circle of diameter `AP` (Thales),
the chord `F_b F_c` has length `PA · sin (∠ B A C)` (inscribed-angle theorem),
and the law of cosines in `△ P F_b F_c` (where `∠ F_b P F_c = π − ∠ B A C`)
gives the identity below.

This was the single open planar-geometry fact; it is now discharged by delegation
to `ErdosMordellChord.chord_identity`, completing the entire Erdős–Mordell
inequality (via `key_inequality_A_of_chord`, the cyclic relabelings for `B`/`C`,
and the algebraic reduction). -/
theorem chord_identity
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    (dist P A * Real.sin (∠ B A C)) ^ 2
      = lineDist P C A ^ 2 + lineDist P A B ^ 2
        + 2 * lineDist P C A * lineDist P A B * Real.cos (∠ B A C) := by
  -- This is exactly `ErdosMordellChord.chord_identity` with `(X, Y, Z) := (A, B, C)`:
  -- both `lineDist` defs unfold to `Metric.infDist P (affineSpan ℝ {·, ·})`, and the
  -- pedal-feet chord identity there was discharged via `chord_cos_eq` (the law-of-cosines
  -- core). See `Proofs/ErdosMordellChordIdentity.lean`.
  exact ErdosMordellChord.chord_identity A B C P hABC hP

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
    dist C A * lineDist P A B + dist A B * lineDist P C A ≤ dist B C * dist P A :=
  key_inequality_A_of_chord A B C P hABC (chord_identity A B C P hABC hP)

/-- Affine independence is invariant under reindexing the three vertices. -/
private theorem affineIndep_rotate {A B C : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C]) : AffineIndependent ℝ ![B, C, A] := by
  rw [affineIndependent_iff_not_collinear_set]
  have e : ({B, C, A} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [e]; exact affineIndependent_iff_not_collinear_set.mp hABC

/-- The interior of the triangle hull is invariant under reindexing the vertices. -/
private theorem mem_interior_hull_rotate {A B C P : EuclideanSpace ℝ (Fin 2)}
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    P ∈ interior (convexHull ℝ ({B, C, A} : Set (EuclideanSpace ℝ (Fin 2)))) := by
  have e : ({B, C, A} : Set (EuclideanSpace ℝ (Fin 2))) = {A, B, C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [e]; exact hP

/-- **Erdős–Mordell key inequality at vertex `B`** (cyclic image of `key_inequality_A`,
obtained by applying it to the relabelled triangle `B C A`). -/
theorem key_inequality_B
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    dist A B * lineDist P B C + dist B C * lineDist P A B ≤ dist C A * dist P B :=
  key_inequality_A B C A P (affineIndep_rotate hABC) (mem_interior_hull_rotate hP)

/-- **Erdős–Mordell key inequality at vertex `C`** (cyclic image of `key_inequality_A`,
obtained by applying it to the relabelled triangle `C A B`). -/
theorem key_inequality_C
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    dist B C * lineDist P C A + dist C A * lineDist P B C ≤ dist A B * dist P C :=
  key_inequality_B B C A P (affineIndep_rotate hABC) (mem_interior_hull_rotate hP)

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
