import Mathlib

/-
# Erdős #659 (OQ): Concrete Euclidean realizations of two-distance 4-point configurations

Erdős problem #659 concerns point sets in the plane with few distinct pairwise
distances. A key object in the classification underlying the problem is the family
of **two-distance sets**: point configurations realizing exactly two distinct
pairwise distances. On four points there are, up to similarity, exactly six such
configurations (square, 60° rhombus, two isosceles trapezoids, a kite, and four
vertices of a regular pentagon); these are enumerated abstractly in
`Erdos659Problem.lean` as the inductive type `TwoDistanceConfig`.

This file supplies the missing **concrete, verified** side of that picture: explicit
four-point configurations together with machine-checked proofs of their pairwise
distance spectra. It is fully self-contained (it imports only Mathlib), `axiom`-free
and `sorry`-free.

## The metric subtlety this file fixes

`Erdos659Problem.lean` measures distances with Mathlib's default `dist` on `ℝ × ℝ`,
which is the **Chebyshev (ℓ∞) product metric**, not the Euclidean one. Under that
metric the unit square `{(0,0),(1,0),(0,1),(1,1)}` degenerates to a *single* distance
(all pairwise `dist`s equal `1`), as that file's own docstring notes. Here we work
with the genuine **Euclidean** squared distance

  `sqDist p q = (p.1 - q.1)^2 + (p.2 - q.2)^2`,

under which the square correctly has the two-element squared-distance spectrum
`{1, 2}`. Working with the *squared* distance keeps every spectrum rational (even for
the 60° rhombus, whose coordinates involve `√3`), so the classification statements are
decided by `norm_num`/`linear_combination` rather than by reasoning about surds.

## Results

* `sqDist` and its basic metric properties (`sqDist_nonneg`, `sqDist_symm`,
  `sqDist_self`, `sqDist_eq_zero_iff`).
* `IsTwoDistance4`: the predicate "these four points realize exactly two distinct
  positive squared distances".
* `unitSquare_isTwoDistance`: the unit square is a two-distance set with spectrum
  `{1, 2}`  (realizes `TwoDistanceConfig.square`).
* `rhombus60_isTwoDistance`: the 60° rhombus (two equilateral triangles glued on an
  edge) is a two-distance set with spectrum `{1, 3}` (realizes
  `TwoDistanceConfig.rhombus`).
* `rectangle_not_isTwoDistance`: a non-square `1 × 2` rectangle is **not** a
  two-distance set — its spectrum is `{1, 4, 5}` (three distances), showing the
  predicate genuinely discriminates.
-/

namespace Erdos659TwoDistance

open scoped Finset

/-- Euclidean squared distance on the plane `ℝ × ℝ`.

This is the honest ℓ² squared distance, *not* the square of Mathlib's default `dist`
on `ℝ × ℝ` (which is the Chebyshev/ℓ∞ metric). -/
def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

@[simp] lemma sqDist_self (p : ℝ × ℝ) : sqDist p p = 0 := by
  unfold sqDist; ring

lemma sqDist_nonneg (p q : ℝ × ℝ) : 0 ≤ sqDist p q := by
  unfold sqDist; positivity

lemma sqDist_symm (p q : ℝ × ℝ) : sqDist p q = sqDist q p := by
  unfold sqDist; ring

lemma sqDist_eq_zero_iff (p q : ℝ × ℝ) : sqDist p q = 0 ↔ p = q := by
  unfold sqDist
  constructor
  · intro h
    have hx : (p.1 - q.1) ^ 2 = 0 := by
      linarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    have hy : (p.2 - q.2) ^ 2 = 0 := by
      linarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
    have hx' : p.1 = q.1 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hx)
    have hy' : p.2 = q.2 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hy)
    exact Prod.ext hx' hy'
  · rintro rfl; ring

/-- The (finite) set of the six unordered pairwise squared distances of four points. -/
noncomputable def sqDistSet4 (a b c d : ℝ × ℝ) : Finset ℝ :=
  {sqDist a b, sqDist a c, sqDist a d, sqDist b c, sqDist b d, sqDist c d}

/-- Four points form a **two-distance set** when they realize exactly two distinct
pairwise squared distances. -/
def IsTwoDistance4 (a b c d : ℝ × ℝ) : Prop :=
  (sqDistSet4 a b c d).card = 2

/-! ### The unit square realizes `TwoDistanceConfig.square` -/

/-- Vertices of the unit square. -/
def s0 : ℝ × ℝ := (0, 0)
def s1 : ℝ × ℝ := (1, 0)
def s2 : ℝ × ℝ := (0, 1)
def s3 : ℝ × ℝ := (1, 1)

/-- The unit square's squared-distance spectrum is exactly `{1, 2}`: the four sides
have squared length `1`, the two diagonals squared length `2`. -/
theorem unitSquare_spectrum : sqDistSet4 s0 s1 s2 s3 = {1, 2} := by
  have h01 : sqDist s0 s1 = 1 := by simp only [sqDist, s0, s1]; norm_num
  have h02 : sqDist s0 s2 = 1 := by simp only [sqDist, s0, s2]; norm_num
  have h03 : sqDist s0 s3 = 2 := by simp only [sqDist, s0, s3]; norm_num
  have h12 : sqDist s1 s2 = 2 := by simp only [sqDist, s1, s2]; norm_num
  have h13 : sqDist s1 s3 = 1 := by simp only [sqDist, s1, s3]; norm_num
  have h23 : sqDist s2 s3 = 1 := by simp only [sqDist, s2, s3]; norm_num
  unfold sqDistSet4
  rw [h01, h02, h03, h12, h13, h23]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The unit square is a two-distance set (realizes `TwoDistanceConfig.square`). -/
theorem unitSquare_isTwoDistance : IsTwoDistance4 s0 s1 s2 s3 := by
  unfold IsTwoDistance4
  rw [unitSquare_spectrum, Finset.card_insert_of_notMem (by norm_num),
    Finset.card_singleton]

/-! ### The 60° rhombus realizes `TwoDistanceConfig.rhombus`

Two unit equilateral triangles glued along the edge `r0 r1`. All four sides and the
short diagonal `r1 r3` have squared length `1`; the long diagonal `r0 r2` has squared
length `3`. The `√3` in the coordinates cancels, leaving the rational spectrum
`{1, 3}`. -/

noncomputable def r0 : ℝ × ℝ := (0, 0)
noncomputable def r1 : ℝ × ℝ := (1, 0)
noncomputable def r2 : ℝ × ℝ := (3 / 2, Real.sqrt 3 / 2)
noncomputable def r3 : ℝ × ℝ := (1 / 2, Real.sqrt 3 / 2)

/-- The 60° rhombus's squared-distance spectrum is exactly `{1, 3}`. -/
theorem rhombus60_spectrum : sqDistSet4 r0 r1 r2 r3 = {1, 3} := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h01 : sqDist r0 r1 = 1 := by simp only [sqDist, r0, r1]; norm_num
  have h02 : sqDist r0 r2 = 3 := by
    simp only [sqDist, r0, r2]; linear_combination (1 / 4 : ℝ) * hs
  have h03 : sqDist r0 r3 = 1 := by
    simp only [sqDist, r0, r3]; linear_combination (1 / 4 : ℝ) * hs
  have h12 : sqDist r1 r2 = 1 := by
    simp only [sqDist, r1, r2]; linear_combination (1 / 4 : ℝ) * hs
  have h13 : sqDist r1 r3 = 1 := by
    simp only [sqDist, r1, r3]; linear_combination (1 / 4 : ℝ) * hs
  have h23 : sqDist r2 r3 = 1 := by
    simp only [sqDist, r2, r3]; ring
  unfold sqDistSet4
  rw [h01, h02, h03, h12, h13, h23]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The 60° rhombus is a two-distance set (realizes `TwoDistanceConfig.rhombus`). -/
theorem rhombus60_isTwoDistance : IsTwoDistance4 r0 r1 r2 r3 := by
  unfold IsTwoDistance4
  rw [rhombus60_spectrum, Finset.card_insert_of_notMem (by norm_num),
    Finset.card_singleton]

/-! ### A non-square rectangle is not a two-distance set -/

def t0 : ℝ × ℝ := (0, 0)
def t1 : ℝ × ℝ := (2, 0)
def t2 : ℝ × ℝ := (0, 1)
def t3 : ℝ × ℝ := (2, 1)

/-- The `1 × 2` rectangle has squared-distance spectrum `{1, 4, 5}`: short sides `1`,
long sides `4`, diagonals `5`. Three distinct distances. -/
theorem rectangle_spectrum : sqDistSet4 t0 t1 t2 t3 = {1, 4, 5} := by
  have h01 : sqDist t0 t1 = 4 := by simp only [sqDist, t0, t1]; norm_num
  have h02 : sqDist t0 t2 = 1 := by simp only [sqDist, t0, t2]; norm_num
  have h03 : sqDist t0 t3 = 5 := by simp only [sqDist, t0, t3]; norm_num
  have h12 : sqDist t1 t2 = 5 := by simp only [sqDist, t1, t2]; norm_num
  have h13 : sqDist t1 t3 = 1 := by simp only [sqDist, t1, t3]; norm_num
  have h23 : sqDist t2 t3 = 4 := by simp only [sqDist, t2, t3]; norm_num
  unfold sqDistSet4
  rw [h01, h02, h03, h12, h13, h23]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The non-square rectangle is **not** a two-distance set: its spectrum has three
elements, so it does not satisfy `IsTwoDistance4`. -/
theorem rectangle_not_isTwoDistance : ¬ IsTwoDistance4 t0 t1 t2 t3 := by
  unfold IsTwoDistance4
  rw [rectangle_spectrum]
  have hcard : ({1, 4, 5} : Finset ℝ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by norm_num),
        Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]
  rw [hcard]
  norm_num

/-- Summary: a square and a 60° rhombus are both two-distance four-point sets, whereas
a non-square rectangle is not — the three distinct realizations of the classification
skeleton, verified. -/
theorem two_distance_examples :
    IsTwoDistance4 s0 s1 s2 s3 ∧ IsTwoDistance4 r0 r1 r2 r3 ∧
      ¬ IsTwoDistance4 t0 t1 t2 t3 :=
  ⟨unitSquare_isTwoDistance, rhombus60_isTwoDistance, rectangle_not_isTwoDistance⟩

end Erdos659TwoDistance
