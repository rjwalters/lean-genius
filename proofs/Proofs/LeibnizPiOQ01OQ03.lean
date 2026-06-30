import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-
  The Complete Arctan Addition Law and Dase's Three-Term π Formula
  (leibniz-pi-oq-01-oq-03)

  The arctangent addition formula is the engine behind every fast,
  arctan-based π series. In its naive form

      arctan x + arctan y = arctan ((x + y) / (1 - x·y)),

  it is only valid when `x·y < 1`: when the product exceeds 1 the right-hand
  arctangent lands in the wrong branch and the true identity acquires a `± π`
  correction. Mathlib exposes the *complete* law as three lemmas
  (`Real.arctan_add`, `Real.arctan_add_eq_add_pi`, `Real.arctan_add_eq_sub_pi`)
  covering the three regimes

      x·y < 1                →  + 0
      x·y > 1,  x > 0        →  + π
      x·y > 1,  x < 0        →  − π.

  The sibling entry `leibniz-pi-oq-01-oq-01` derives **Machin's** two-term
  formula but only ever uses the `x·y < 1` branch. Here we (i) package the
  *full* addition law — all three regimes — together with the derived
  subtraction and doubling laws, then (ii) apply it to prove **Dase's
  three-term formula**

      π/4 = arctan(1/2) + arctan(1/5) + arctan(1/8),

  a decomposition into *three* small arctangents (used by Zacharias Dase in
  1844 to compute 200 digits of π by hand) that is present in neither Mathlib
  nor the sibling entry. Everything is machine-checked and axiom-free.
-/

namespace LeibnizPiOQ01OQ03

open Real

/-! ### The complete arctan addition law (three regimes) -/

/-- **Addition law, principal branch** (`x·y < 1`): packaged from
    `Real.arctan_add`. -/
theorem arctan_add_lt {x y : ℝ} (h : x * y < 1) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) :=
  Real.arctan_add h

/-- **Addition law, upper branch** (`x·y > 1`, `x > 0`): a `+π` correction is
    required.  Packaged from `Real.arctan_add_eq_add_pi`. -/
theorem arctan_add_gt_pos {x y : ℝ} (h : 1 < x * y) (hx : 0 < x) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) + π :=
  Real.arctan_add_eq_add_pi h hx

/-- **Addition law, lower branch** (`x·y > 1`, `x < 0`): a `−π` correction is
    required.  Packaged from `Real.arctan_add_eq_sub_pi`. -/
theorem arctan_add_gt_neg {x y : ℝ} (h : 1 < x * y) (hx : x < 0) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) - π :=
  Real.arctan_add_eq_sub_pi h hx

/-- **Subtraction law** (`-(x·y) < 1`).  Derived from the principal-branch
    addition law applied to `x` and `-y`, using `arctan (-y) = -arctan y`. -/
theorem arctan_sub {x y : ℝ} (h : -(x * y) < 1) :
    arctan x - arctan y = arctan ((x - y) / (1 + x * y)) := by
  have hxy : x * (-y) < 1 := by simpa [mul_neg] using h
  have hadd := Real.arctan_add hxy
  rw [Real.arctan_neg] at hadd
  rw [sub_eq_add_neg, hadd]
  congr 1
  ring

/-- **Doubling law** (`-1 < x < 1`): packaged from `Real.two_mul_arctan`. -/
theorem two_arctan {x : ℝ} (h₁ : -1 < x) (h₂ : x < 1) :
    2 * arctan x = arctan (2 * x / (1 - x ^ 2)) :=
  Real.two_mul_arctan h₁ h₂

/-! ### Worked applications: two- and three-term π/4 decompositions -/

/-- **Euler's two-term formula**: `arctan(1/2) + arctan(1/3) = π/4`, recovered
    in one line from the principal-branch addition law (the argument simplifies
    to `1`).  Mathlib states this as `arctan_inv_2_add_arctan_inv_3`; here it
    falls straight out of `arctan_add_lt`. -/
theorem euler_two_term : arctan (1 / 2) + arctan (1 / 3) = π / 4 := by
  have h : arctan (1 / 2) + arctan (1 / 3) = arctan 1 := by
    rw [arctan_add_lt (by norm_num)]
    congr 1
    norm_num
  rw [h, arctan_one]

/-- **Dase's three-term formula** (1844): `π/4 = arctan(1/2) + arctan(1/5) + arctan(1/8)`.

    Two applications of the principal-branch addition law:
    `arctan(1/2) + arctan(1/5) = arctan(7/9)`, then
    `arctan(7/9) + arctan(1/8) = arctan(1) = π/4`, the final step turning on the
    cancellation `(7/9 + 1/8)/(1 - 7/72) = (65/72)/(65/72) = 1`. -/
theorem dase_three_term :
    arctan (1 / 2) + arctan (1 / 5) + arctan (1 / 8) = π / 4 := by
  have h1 : arctan (1 / 2) + arctan (1 / 5) = arctan (7 / 9) := by
    rw [arctan_add_lt (by norm_num)]
    congr 1
    norm_num
  have h2 : arctan (7 / 9) + arctan (1 / 8) = arctan 1 := by
    rw [arctan_add_lt (by norm_num)]
    congr 1
    norm_num
  rw [h1, h2, arctan_one]

/-- Dase's formula solved for `π`: `π = 4·arctan(1/2) + 4·arctan(1/5) + 4·arctan(1/8)`. -/
theorem dase_pi :
    π = 4 * arctan (1 / 2) + 4 * arctan (1 / 5) + 4 * arctan (1 / 8) := by
  have := dase_three_term
  linarith

/-- Sanity check via tangents: the tangent of Dase's right-hand side is `1`,
    confirming the angle equals `π/4` (the addition arithmetic is `tan`-consistent). -/
theorem tan_dase_rhs :
    Real.tan (arctan (1 / 2) + arctan (1 / 5) + arctan (1 / 8)) = 1 := by
  rw [dase_three_term, show (π / 4 : ℝ) = arctan 1 from arctan_one.symm, tan_arctan]

end LeibnizPiOQ01OQ03
