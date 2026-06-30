import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-
# The Tangent Addition Law and the Triangle Tangent Identities

## What This Proves

Starting from the tangent addition law, this file builds up to two classical
*triangle* identities that are **not** in Mathlib:

* **Triple tangent identity.** If `A + B + C = π` (the angles of a triangle)
  and none of the angles is a right angle, then
  `tan A + tan B + tan C = tan A · tan B · tan C`.
  The sum of the tangents equals their product — a striking fact with no
  analogue for sine or cosine.

* **Triple cotangent identity.** Under the same angle-sum constraint (with no
  angle equal to `0` or `π`),
  `cot A · cot B + cot B · cot C + cot C · cot A = 1`.

Both reduce to a single symmetric polynomial identity in the sines and cosines
of the three angles, `sin_cos_triangle_identity`, which is the mathematical
heart of the file.

## Relation to Mathlib

Mathlib already provides the *two-argument* tangent laws
(`Real.tan_add`, `Real.tan_add'`, `Real.tan_sub`, `Real.tan_two_mul`) and the
arctangent addition law (`Real.arctan_add`), but it states them with the
hypothesis `∀ k : ℤ, x ≠ (2 k + 1) * π / 2`. We first repackage addition and
subtraction with the more usable hypothesis `cos x ≠ 0` (equivalent via
`Real.cos_eq_zero_iff`), then prove the genuinely new three-angle identities.

As a concrete application on rational tangents we derive
`arctan (1/2) + arctan (1/3) = π/4`, connecting to the gallery's
`MachinFromAddition` entry from the tangent side.
-/

namespace TangentAdditionFormula

open Real

variable {x y A B C : ℝ}

/-- **Tangent addition law, `cos ≠ 0` form.** This is `Real.tan_add'` restated
with the directly checkable hypotheses `cos x ≠ 0`, `cos y ≠ 0`
(equivalent to "`x`, `y` are not odd multiples of `π/2`" by
`Real.cos_eq_zero_iff`). -/
theorem tan_add_of_cos_ne_zero (hx : cos x ≠ 0) (hy : cos y ≠ 0) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  refine Real.tan_add' ⟨fun k => ?_, fun l => ?_⟩
  · intro hk; exact hx (cos_eq_zero_iff.mpr ⟨k, hk⟩)
  · intro hl; exact hy (cos_eq_zero_iff.mpr ⟨l, hl⟩)

/-- **Tangent subtraction law, `cos ≠ 0` form.** The companion of
`tan_add_of_cos_ne_zero`, with the characteristic `1 + tan x · tan y`
denominator. -/
theorem tan_sub_of_cos_ne_zero (hx : cos x ≠ 0) (hy : cos y ≠ 0) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
  refine Real.tan_sub' ⟨fun k => ?_, fun l => ?_⟩
  · intro hk; exact hx (cos_eq_zero_iff.mpr ⟨k, hk⟩)
  · intro hl; exact hy (cos_eq_zero_iff.mpr ⟨l, hl⟩)

/-- **The symmetric trigonometric heart.** For three angles summing to `π`,
`sin A cos B cos C + sin B cos A cos C + sin C cos A cos B = sin A sin B sin C`.

Both triple identities below are this polynomial identity divided by an
appropriate product of sines or cosines. It is proved by eliminating `C` via
`C = π - (A + B)` and expanding with the two-argument addition laws. -/
theorem sin_cos_triangle_identity (h : A + B + C = π) :
    sin A * cos B * cos C + sin B * cos A * cos C + sin C * cos A * cos B
      = sin A * sin B * sin C := by
  have hC : C = π - (A + B) := by linarith
  rw [hC, sin_pi_sub, cos_pi_sub, sin_add, cos_add]
  ring

/-- **Triple tangent identity.** For the angles of a (possibly degenerate)
triangle, `A + B + C = π`, with no angle a right angle (`cos · ≠ 0`),
the sum of the tangents equals their product:
`tan A + tan B + tan C = tan A · tan B · tan C`. Not in Mathlib. -/
theorem tan_sum_eq_tan_prod (h : A + B + C = π)
    (hA : cos A ≠ 0) (hB : cos B ≠ 0) (hC : cos C ≠ 0) :
    tan A + tan B + tan C = tan A * tan B * tan C := by
  have e1 : tan A + tan B + tan C
      = (sin A * cos B * cos C + sin B * cos A * cos C + sin C * cos A * cos B)
          / (cos A * cos B * cos C) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    field_simp
  have e2 : tan A * tan B * tan C
      = sin A * sin B * sin C / (cos A * cos B * cos C) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    field_simp
  rw [e1, e2, sin_cos_triangle_identity h]

/-- **Triple cotangent identity.** For `A + B + C = π` with no angle a multiple
of `π` (`sin · ≠ 0`), the pairwise products of cotangents sum to `1`:
`cot A · cot B + cot B · cot C + cot C · cot A = 1`. Not in Mathlib. -/
theorem cot_sum_eq_one (h : A + B + C = π)
    (hA : sin A ≠ 0) (hB : sin B ≠ 0) (hC : sin C ≠ 0) :
    cot A * cot B + cot B * cot C + cot C * cot A = 1 := by
  have e : cot A * cot B + cot B * cot C + cot C * cot A
      = (cos A * cos B * sin C + cos B * cos C * sin A + cos C * cos A * sin B)
          / (sin A * sin B * sin C) := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
    field_simp
  rw [e, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hA hB) hC)]
  linear_combination sin_cos_triangle_identity h

/-- **Concrete application on rational tangents.**
`arctan (1/2) + arctan (1/3) = π/4`. The two right-triangle angles with leg
ratios `1:2` and `1:3` add to half a right angle — the tangent addition law
applied to `tan = 1/2, 1/3` lands exactly on `tan = 1`. -/
theorem arctan_half_add_arctan_third :
    arctan (1 / 2) + arctan (1 / 3) = π / 4 := by
  have harg : ((1 : ℝ) / 2 + 1 / 3) / (1 - 1 / 2 * (1 / 3)) = 1 := by norm_num
  rw [arctan_add (by norm_num), harg, arctan_one]

/-- The equilateral instance of the triple tangent identity: with all three
angles equal to `π/3`, both sides equal `3√3`. A concrete check that the
centerpiece theorem applies. -/
example :
    tan (π / 3) + tan (π / 3) + tan (π / 3)
      = tan (π / 3) * tan (π / 3) * tan (π / 3) := by
  have h : π / 3 + π / 3 + π / 3 = π := by ring
  have hcos : cos (π / 3) ≠ 0 := by rw [cos_pi_div_three]; norm_num
  exact tan_sum_eq_tan_prod h hcos hcos hcos

end TangentAdditionFormula
