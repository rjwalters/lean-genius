import Mathlib

/-!
# The inverse hyperbolic sine: logarithmic form and addition law

The inverse hyperbolic sine `arsinh : ℝ → ℝ` is, by definition in Mathlib,
`arsinh x = log (x + √(1 + x²))`. It is the bijective inverse of `sinh` and the
antiderivative of `1/√(1 + x²)`.

Mathlib provides the inverse-pair facts (`Real.sinh_arsinh`, `Real.arsinh_sinh`),
the Pythagorean companion (`Real.cosh_arsinh`), and the defining `Real.exp_arsinh`,
but it does **not** record:

* the **closed logarithmic form** as a named lemma (`arsinh_eq_log`);
* the **addition law** `arsinh x + arsinh y = arsinh (x·√(1+y²) + y·√(1+x²))`,
  the inverse-hyperbolic analogue of `arctan`'s addition formula — together with
  its **subtraction** and **doubling** corollaries;
* concrete **closed-form values** such as `arsinh (3/4) = log 2` and
  `arsinh (4/3) = log 3`.

This file supplies those. The headline closed form is `rfl` against the Mathlib
definition (hence the `mathlib` badge), while the addition / subtraction / doubling
laws and the concrete values are genuinely new derived content, all fully
machine-checked. The inverse-hyperbolic sine and its closed form are absent from the
gallery, whose only inverse-hyperbolic content is `arctanh` (Poincaré-disk metric).
-/

namespace ArsinhLogFormulaOQ01

open Real

/-! ## The closed logarithmic form -/

/-- **Closed logarithmic form of `arsinh`.** `arsinh x = log (x + √(1 + x²))`.
This is the definitional unfolding, named for stable reference. -/
theorem arsinh_eq_log (x : ℝ) : arsinh x = Real.log (x + Real.sqrt (1 + x ^ 2)) := rfl

/-- The exponential form `exp (arsinh x) = x + √(1 + x²)` (re-exported from Mathlib). -/
theorem exp_arsinh' (x : ℝ) : Real.exp (arsinh x) = x + Real.sqrt (1 + x ^ 2) :=
  Real.exp_arsinh x

/-! ## Inverse-pair and Pythagorean companion (re-exported) -/

/-- `sinh` is a left inverse of `arsinh`: `sinh (arsinh x) = x`. -/
theorem sinh_arsinh' (x : ℝ) : Real.sinh (arsinh x) = x := Real.sinh_arsinh x

/-- `arsinh` is a left inverse of `sinh`: `arsinh (sinh x) = x`. -/
theorem arsinh_sinh' (x : ℝ) : arsinh (Real.sinh x) = x := Real.arsinh_sinh x

/-- **Pythagorean companion.** `cosh (arsinh x) = √(1 + x²)`; the identity that turns
`∫ dx/√(1+x²)` into `arsinh`. -/
theorem cosh_arsinh' (x : ℝ) : Real.cosh (arsinh x) = Real.sqrt (1 + x ^ 2) :=
  Real.cosh_arsinh x

/-- `arsinh` is odd: `arsinh (-x) = -arsinh x` (re-exported). -/
theorem arsinh_neg' (x : ℝ) : arsinh (-x) = -arsinh x := Real.arsinh_neg x

/-! ## The addition law and its corollaries (new) -/

/-- **Addition law for `arsinh`.**
`arsinh x + arsinh y = arsinh (x·√(1+y²) + y·√(1+x²))`.
This is the inverse-hyperbolic analogue of the arctangent addition formula; it is
not in Mathlib. Proof: apply `arsinh` to `sinh (arsinh x + arsinh y)`, expand with
`sinh_add` and the inverse-pair / Pythagorean identities. -/
theorem arsinh_add (x y : ℝ) :
    arsinh x + arsinh y =
      arsinh (x * Real.sqrt (1 + y ^ 2) + y * Real.sqrt (1 + x ^ 2)) := by
  rw [← Real.arsinh_sinh (arsinh x + arsinh y)]
  congr 1
  simp only [Real.sinh_add, Real.sinh_arsinh, Real.cosh_arsinh]
  ring

/-- **Subtraction law for `arsinh`.**
`arsinh x - arsinh y = arsinh (x·√(1+y²) - y·√(1+x²))`. -/
theorem arsinh_sub (x y : ℝ) :
    arsinh x - arsinh y =
      arsinh (x * Real.sqrt (1 + y ^ 2) - y * Real.sqrt (1 + x ^ 2)) := by
  rw [sub_eq_add_neg, ← Real.arsinh_neg, arsinh_add]
  congr 1
  rw [neg_sq]
  ring

/-- **Doubling law for `arsinh`.** `2 · arsinh x = arsinh (2x·√(1+x²))`. -/
theorem two_arsinh (x : ℝ) :
    2 * arsinh x = arsinh (2 * x * Real.sqrt (1 + x ^ 2)) := by
  rw [two_mul, arsinh_add]
  congr 1
  ring

/-! ## Concrete closed-form values (new) -/

/-- `arsinh (3/4) = log 2`. Check: `√(1 + (3/4)²) = 5/4` and `3/4 + 5/4 = 2`. -/
theorem arsinh_three_quarters : arsinh (3 / 4) = Real.log 2 := by
  rw [arsinh_eq_log]
  have h : Real.sqrt (1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
    rw [show (1 + (3 / 4 : ℝ) ^ 2) = (5 / 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h, show (3 / 4 + 5 / 4 : ℝ) = 2 by norm_num]

/-- `arsinh (4/3) = log 3`. Check: `√(1 + (4/3)²) = 5/3` and `4/3 + 5/3 = 3`. -/
theorem arsinh_four_thirds : arsinh (4 / 3) = Real.log 3 := by
  rw [arsinh_eq_log]
  have h : Real.sqrt (1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show (1 + (4 / 3 : ℝ) ^ 2) = (5 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h, show (4 / 3 + 5 / 3 : ℝ) = 3 by norm_num]

end ArsinhLogFormulaOQ01
