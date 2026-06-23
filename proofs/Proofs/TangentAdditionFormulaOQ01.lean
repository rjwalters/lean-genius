import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-
# The Three-Argument Tangent Addition Law

## What This Proves

The parent entry `TangentAdditionFormula` establishes the two-argument tangent
law `tan (x + y) = (tan x + tan y)/(1 - tan x · tan y)`, the triangle tangent
identity for `A + B + C = π`, and a Machin-style numeric application. This
follow-up proves the genuinely more general **three-argument** law and its
diagonal corollary, neither of which is in Mathlib nor in the parent.

* **Three-argument addition law.** For angles with `cos x, cos y, cos z ≠ 0`
  and `cos (x + y + z) ≠ 0`,
  `tan (x + y + z) = (e₁ - e₃) / (1 - e₂)`,
  where `e₁ = tan x + tan y + tan z`, `e₂ = tan x·tan y + tan y·tan z + tan z·tan x`,
  and `e₃ = tan x·tan y·tan z` are the elementary symmetric polynomials in the
  three tangents. This is the tangent analogue of the symmetric-function shape
  of `sin`/`cos` of a triple sum.

* **Triple-angle formula.** The diagonal `x = y = z` gives the classical
  `tan (3x) = (3 tan x - tan³ x)/(1 - 3 tan² x)`.

* **Unification.** The parent's triangle identity `tan A + tan B + tan C =
  tan A · tan B · tan C` (for `A + B + C = π`) is recovered as the special case
  `tan (A + B + C) = tan π = 0`: the numerator `e₁ - e₃` must vanish.

## Method

We avoid the fragile nested-fraction route. Writing everything over the common
denominator `cos x · cos y · cos z`, the numerator and denominator of the claimed
formula are exactly the expansions of `sin (x + y + z)` and `cos (x + y + z)`
(via `sin_add`/`cos_add`). The law then collapses to the cancellation
`(N/c)/(D/c) = N/D` (`div_div_div_cancel_right₀`). The triple-angle formula is a
one-line `ring` specialization, and the triangle identity follows from
`div_eq_zero_iff` once the denominator is shown nonzero.
-/

open Real

variable {x y z A B C : ℝ}

/-- **Three-argument tangent addition law.** With the directly checkable
side-conditions `cos x, cos y, cos z ≠ 0` and `cos (x + y + z) ≠ 0`,
`tan (x + y + z)` equals `(e₁ - e₃)/(1 - e₂)` in the elementary symmetric
polynomials of `tan x, tan y, tan z`. Not in Mathlib. -/
theorem tan_add_three (hx : cos x ≠ 0) (hy : cos y ≠ 0) (hz : cos z ≠ 0)
    (hxyz : cos (x + y + z) ≠ 0) :
    tan (x + y + z)
      = (tan x + tan y + tan z - tan x * tan y * tan z)
          / (1 - (tan x * tan y + tan y * tan z + tan z * tan x)) := by
  have hcc : cos x * cos y * cos z ≠ 0 := mul_ne_zero (mul_ne_zero hx hy) hz
  have hs : sin (x + y + z)
      = sin x * cos y * cos z + cos x * sin y * cos z + cos x * cos y * sin z
          - sin x * sin y * sin z := by
    rw [show x + y + z = (x + y) + z from by ring, sin_add, sin_add, cos_add]; ring
  have hc : cos (x + y + z)
      = cos x * cos y * cos z - sin x * sin y * cos z - sin x * cos y * sin z
          - cos x * sin y * sin z := by
    rw [show x + y + z = (x + y) + z from by ring, cos_add, sin_add, cos_add]; ring
  have hnum : tan x + tan y + tan z - tan x * tan y * tan z
      = (sin x * cos y * cos z + cos x * sin y * cos z + cos x * cos y * sin z
          - sin x * sin y * sin z) / (cos x * cos y * cos z) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]; field_simp <;> ring
  have hden : 1 - (tan x * tan y + tan y * tan z + tan z * tan x)
      = (cos x * cos y * cos z - sin x * sin y * cos z - sin x * cos y * sin z
          - cos x * sin y * sin z) / (cos x * cos y * cos z) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]; field_simp <;> ring
  rw [tan_eq_sin_div_cos, hs, hc, hnum, hden, div_div_div_cancel_right₀ hcc]

/-- **Triple-angle tangent formula.** The `x = y = z` diagonal of the
three-argument law: `tan (3x) = (3 tan x - tan³ x)/(1 - 3 tan² x)`, for
`cos x ≠ 0` and `cos (3x) ≠ 0`. -/
theorem tan_three_mul (hx : cos x ≠ 0) (h3x : cos (3 * x) ≠ 0) :
    tan (3 * x) = (3 * tan x - tan x ^ 3) / (1 - 3 * tan x ^ 2) := by
  have hxyz : cos (x + x + x) ≠ 0 := by rw [show x + x + x = 3 * x from by ring]; exact h3x
  rw [show 3 * x = x + x + x from by ring, tan_add_three hx hx hx hxyz]
  ring

/-- **Triangle tangent identity, recovered from the general law.** For
`A + B + C = π` with no angle a right angle, the parent's
`tan A + tan B + tan C = tan A · tan B · tan C` is exactly the statement that the
numerator `e₁ - e₃` of `tan (A + B + C) = tan π = 0` vanishes. -/
theorem tan_sum_eq_tan_prod_of_three (h : A + B + C = π)
    (hA : cos A ≠ 0) (hB : cos B ≠ 0) (hC : cos C ≠ 0) :
    tan A + tan B + tan C = tan A * tan B * tan C := by
  have hABC : cos (A + B + C) ≠ 0 := by rw [h, cos_pi]; norm_num
  have hcc : cos A * cos B * cos C ≠ 0 := mul_ne_zero (mul_ne_zero hA hB) hC
  -- the denominator `1 - e₂` is nonzero because `cos (A+B+C) = (cos A cos B cos C)·(1 - e₂)`
  have hden_ne : (1 : ℝ) - (tan A * tan B + tan B * tan C + tan C * tan A) ≠ 0 := by
    have hexp : cos (A + B + C)
        = cos A * cos B * cos C
            * (1 - (tan A * tan B + tan B * tan C + tan C * tan A)) := by
      rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos,
        show A + B + C = (A + B) + C from by ring, cos_add, sin_add, cos_add]
      field_simp <;> ring
    intro hzero
    exact hABC (by rw [hexp, hzero, mul_zero])
  have key := tan_add_three hA hB hC hABC
  rw [h, tan_pi] at key
  rw [eq_comm, div_eq_zero_iff] at key
  rcases key with hnum | hbad
  · linarith
  · exact absurd hbad hden_ne

