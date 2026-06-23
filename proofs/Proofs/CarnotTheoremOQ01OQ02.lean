import Mathlib
import Proofs.CarnotTheorem

/-
# Carnot's Theorem — the squared cosine form and the acute/right/obtuse trichotomy

The parent file `CarnotTheorem.lean` proves the **fundamental (squared) cosine
identity** for the angles of a triangle (any reals with `A + B + C = π`),

  `cos²A + cos²B + cos²C + 2 cos A cos B cos C = 1`.

Read as a statement about the single product `P := cos A cos B cos C`, this is

  `cos²A + cos²B + cos²C = 1 - 2 P`,

so the value of the squared cosine sum is governed entirely by the **sign of the
product of cosines**. For an actual triangle (`A, B, C > 0`, `A + B + C = π`) the
sign of `P` is in turn fixed by the triangle's type, because at most one angle can
be `≥ π/2`:

* **acute**  (all angles `< π/2`)  ⟹ all three cosines are positive ⟹ `P > 0`;
* **right**  (one angle `= π/2`)   ⟹ that cosine is `0` ⟹ `P = 0`;
* **obtuse** (one angle `> π/2`)   ⟹ that cosine is negative while the other two
  are positive (their angles are forced below `π/2`) ⟹ `P < 0`.

Feeding these signs through `cos²A + cos²B + cos²C = 1 - 2P` yields the clean
trichotomy

  `cos²A + cos²B + cos²C  <  1`  ⟺  the triangle is acute,
  `cos²A + cos²B + cos²C  =  1`  ⟺  the triangle is right,
  `cos²A + cos²B + cos²C  >  1`  ⟺  the triangle is obtuse.

This file proves the identity in `1 - 2P` form, each of the three directional
statements, and the capstone iff `cos²A + cos²B + cos²C < 1 ↔ all angles acute`.
Everything is built on the parent's verified `carnot_cos_sq_sum`, the FTC-free
cosine-sign lemmas in Mathlib, and the elementary fact that two angles of a
triangle cannot both reach `π/2`.

**No axioms, no sorries.**
-/

open Real

namespace CarnotTheoremOQ01OQ02

/-- For `x ∈ (0, π/2)` the cosine is positive. A thin wrapper around
`Real.cos_pos_of_mem_Ioo` supplying the (automatic) lower bound `-(π/2) < x`. -/
private theorem cos_pos_of_lt {x : ℝ} (hx0 : 0 < x) (hx : x < π / 2) :
    0 < Real.cos x :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx⟩

/-- **Squared cosine identity, rearranged.**  For any reals with `A + B + C = π`,
`cos²A + cos²B + cos²C = 1 - 2 (cos A cos B cos C)`.

This is the parent's fundamental identity `carnot_cos_sq_sum` solved for the
squared sum; it exhibits the sum as `1` minus twice the product of cosines, the
form that drives the acute/right/obtuse trichotomy below. -/
theorem cos_sq_sum (A B C : ℝ) (h : A + B + C = π) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2
      = 1 - 2 * (Real.cos A * Real.cos B * Real.cos C) := by
  linear_combination CarnotTheorem.carnot_cos_sq_sum A B C h

/-- **Right triangle.**  If one angle is `π/2` then
`cos²A + cos²B + cos²C = 1`.

The right-angle cosine vanishes, so the product term drops out of
`cos²A + cos²B + cos²C = 1 - 2(cos A cos B cos C)`. (Stated for `C = π/2`; the
other two cases follow by symmetry of the hypotheses.) -/
theorem cos_sq_sum_eq_one_of_right (A B C : ℝ) (h : A + B + C = π)
    (hC : C = π / 2) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 = 1 := by
  have hid := cos_sq_sum A B C h
  rw [hC, Real.cos_pi_div_two] at hid ⊢
  simpa using hid

/-- **Acute triangle.**  If all three angles are below `π/2` then
`cos²A + cos²B + cos²C < 1`.

All three cosines are positive, so the product `cos A cos B cos C` is positive and
`1 - 2(cos A cos B cos C) < 1`. -/
theorem cos_sq_sum_lt_one_of_acute (A B C : ℝ)
    (hA0 : 0 < A) (hB0 : 0 < B) (hC0 : 0 < C) (h : A + B + C = π)
    (hA : A < π / 2) (hB : B < π / 2) (hC : C < π / 2) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 < 1 := by
  have pA : 0 < Real.cos A := cos_pos_of_lt hA0 hA
  have pB : 0 < Real.cos B := cos_pos_of_lt hB0 hB
  have pC : 0 < Real.cos C := cos_pos_of_lt hC0 hC
  have hP : 0 < Real.cos A * Real.cos B * Real.cos C := mul_pos (mul_pos pA pB) pC
  have hid := cos_sq_sum A B C h
  linarith [hid, hP]

/-- **Obtuse triangle.**  If one angle exceeds `π/2` then
`1 < cos²A + cos²B + cos²C`.

The obtuse angle's cosine is negative; the remaining two angles sum to less than
`π/2`, so each is acute with positive cosine. Hence `cos A cos B cos C < 0` and
`1 - 2(cos A cos B cos C) > 1`. (Stated for `C` obtuse; the other cases are
symmetric.) -/
theorem cos_sq_sum_gt_one_of_obtuse (A B C : ℝ)
    (hA0 : 0 < A) (hB0 : 0 < B) (hC0 : 0 < C) (h : A + B + C = π)
    (hC : π / 2 < C) :
    1 < Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 := by
  have hA : A < π / 2 := by linarith
  have hB : B < π / 2 := by linarith
  have pA : 0 < Real.cos A := cos_pos_of_lt hA0 hA
  have pB : 0 < Real.cos B := cos_pos_of_lt hB0 hB
  have nC : Real.cos C < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hC (by linarith)
  have hP : Real.cos A * Real.cos B * Real.cos C < 0 :=
    mul_neg_of_pos_of_neg (mul_pos pA pB) nC
  have hid := cos_sq_sum A B C h
  linarith [hid, hP]

/-- If the first angle is `≥ π/2`, the squared cosine sum is `≥ 1`.  The other
two angles are then forced strictly below `π/2`, so their cosines are positive
while the first cosine is nonpositive, giving `cos A cos B cos C ≤ 0`. This is the
non-strict workhorse behind the trichotomy iff. -/
private theorem cos_sq_sum_ge_one_of_ge (A B C : ℝ)
    (hB0 : 0 < B) (hC0 : 0 < C) (h : A + B + C = π) (hA : π / 2 ≤ A) :
    1 ≤ Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 := by
  have hB : B < π / 2 := by linarith
  have hC : C < π / 2 := by linarith
  have pB : 0 < Real.cos B := cos_pos_of_lt hB0 hB
  have pC : 0 < Real.cos C := cos_pos_of_lt hC0 hC
  have nA : Real.cos A ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hA (by linarith)
  have hP : Real.cos A * Real.cos B * Real.cos C ≤ 0 := by
    have hpBC : 0 < Real.cos B * Real.cos C := mul_pos pB pC
    nlinarith [hpBC, nA]
  have hid := cos_sq_sum A B C h
  linarith [hid, hP]

/-- **Trichotomy capstone.**  For a triangle (`A, B, C > 0`, `A + B + C = π`),
`cos²A + cos²B + cos²C < 1` if and only if the triangle is acute (all three
angles `< π/2`).

Backward is `cos_sq_sum_lt_one_of_acute`. Forward is its contrapositive: if some
angle is `≥ π/2` then `cos_sq_sum_ge_one_of_ge` (applied with that angle first)
gives `cos²A + cos²B + cos²C ≥ 1`. Together with the `= 1` right case and the
`> 1` obtuse case this pins the full classification:
`< 1 ⟺ acute`, `= 1 ⟺ right`, `> 1 ⟺ obtuse`. -/
theorem cos_sq_sum_lt_one_iff_acute (A B C : ℝ)
    (hA0 : 0 < A) (hB0 : 0 < B) (hC0 : 0 < C) (h : A + B + C = π) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 < 1
      ↔ A < π / 2 ∧ B < π / 2 ∧ C < π / 2 := by
  constructor
  · intro hlt
    refine ⟨?_, ?_, ?_⟩
    · by_contra hge
      push_neg at hge
      have := cos_sq_sum_ge_one_of_ge A B C hB0 hC0 h hge
      linarith
    · by_contra hge
      push_neg at hge
      have := cos_sq_sum_ge_one_of_ge B A C hA0 hC0 (by linarith) hge
      linarith
    · by_contra hge
      push_neg at hge
      have := cos_sq_sum_ge_one_of_ge C A B hA0 hB0 (by linarith) hge
      linarith
  · rintro ⟨hA, hB, hC⟩
    exact cos_sq_sum_lt_one_of_acute A B C hA0 hB0 hC0 h hA hB hC

end CarnotTheoremOQ01OQ02
