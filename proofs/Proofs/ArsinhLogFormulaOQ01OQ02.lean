/-
# The inverse hyperbolic cosine: logarithmic form and addition law

Research: arsinh-log-formula-oq-01-oq-02
Parent:   arsinh-log-formula-oq-01 (logarithmic form + addition law of `arsinh`)

This file answers the parent's second listed open question verbatim:

  > Prove the companion `arcosh` logarithmic form `arcosh x = log(x + √(x² − 1))`
  > for `x ≥ 1` and its addition law, the `cosh`-side counterpart to this entry.

The parent developed the algebraic theory of `arsinh` — its logarithmic closed
form `arsinh x = log(x + √(1 + x²))`, the addition / subtraction / doubling laws
`arsinh x ± arsinh y = arsinh (x·√(1+y²) ± y·√(1+x²))`, and concrete values.
Here we supply the **`cosh`-side counterpart**: the same theory for `arcosh`,
the inverse of `cosh` restricted to `[1, ∞)`.

Mathlib (`Mathlib.Analysis.SpecialFunctions.Arcosh`) *defines* `Real.arcosh x`
to be `log (x + √(x² − 1))`, so the logarithmic form is definitional (the
`mathlib` badge content), and it supplies the inverse facts `cosh_arcosh`,
`sinh_arcosh`, `arcosh_cosh`. What is **absent from Mathlib** — and is the
original content here — is the family of *algebraic addition formulas*:

* `arcosh_eq_log` — the logarithmic closed form, stated as a named lemma.
* `arcosh_add`     — `arcosh x + arcosh y = arcosh (x·y + √(x²−1)·√(y²−1))`
  for `x, y ≥ 1`, the `cosh`-angle-addition counterpart of the parent's
  `arsinh` addition law.
* `arcosh_sub`     — the subtraction law `arcosh x − arcosh y =
  arcosh (x·y − √(x²−1)·√(y²−1))` for `1 ≤ y ≤ x`.
* `two_mul_arcosh` — the doubling law `2 · arcosh x = arcosh (2x² − 1)`.
* `arcosh_five_quarters`, `arcosh_five_thirds` — concrete evaluations
  `arcosh (5/4) = log 2` and `arcosh (5/3) = log 3`, the `cosh`-side mirror of
  the parent's `arsinh (3/4) = log 2`, `arsinh (4/3) = log 3`.

All results are `0`-axiom and machine-checked.
-/
import Mathlib

namespace ArsinhLogFormulaOQ01OQ02

open Real

/-- **Logarithmic form (the open question).** `arcosh x = log (x + √(x² − 1))`.

In Mathlib this is the *definition* of `Real.arcosh`, so the identity holds by
`rfl`; we record it as a named lemma matching the parent's `arsinh_eq_log`. -/
theorem arcosh_eq_log (x : ℝ) :
    arcosh x = Real.log (x + Real.sqrt (x ^ 2 - 1)) := rfl

/-- Helper: for `x ≥ 1` the radicand `x² − 1` is nonnegative, so
`√(x² − 1) · √(x² − 1) = x² − 1`. -/
theorem sqrt_sq_sub_one_mul_self {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) = x ^ 2 - 1 :=
  Real.mul_self_sqrt (by nlinarith)

/-- **Addition law for `arcosh`.** For `x, y ≥ 1`,
`arcosh x + arcosh y = arcosh (x·y + √(x²−1)·√(y²−1))`.

This is the `cosh`-side counterpart of the parent's `arsinh` addition law: it
comes from `cosh (a + b) = cosh a cosh b + sinh a sinh b` applied to
`a = arcosh x`, `b = arcosh y`, using `cosh (arcosh x) = x` and
`sinh (arcosh x) = √(x² − 1)`. -/
theorem arcosh_add {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    arcosh x + arcosh y =
      arcosh (x * y + Real.sqrt (x ^ 2 - 1) * Real.sqrt (y ^ 2 - 1)) := by
  have ha : 0 ≤ arcosh x := arcosh_nonneg hx
  have hb : 0 ≤ arcosh y := arcosh_nonneg hy
  have hcosh : Real.cosh (arcosh x + arcosh y)
      = x * y + Real.sqrt (x ^ 2 - 1) * Real.sqrt (y ^ 2 - 1) := by
    rw [Real.cosh_add, cosh_arcosh hx, cosh_arcosh hy, sinh_arcosh hx, sinh_arcosh hy]
  rw [← hcosh, arcosh_cosh (add_nonneg ha hb)]

/-- **Subtraction law for `arcosh`.** For `1 ≤ y ≤ x`,
`arcosh x − arcosh y = arcosh (x·y − √(x²−1)·√(y²−1))`.

Dual to `arcosh_add`, from `cosh (a − b) = cosh a cosh b − sinh a sinh b`. The
hypothesis `y ≤ x` guarantees `arcosh y ≤ arcosh x`, so the difference is in the
domain `[0, ∞)` where `arcosh` inverts `cosh`. -/
theorem arcosh_sub {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    arcosh x - arcosh y =
      arcosh (x * y - Real.sqrt (x ^ 2 - 1) * Real.sqrt (y ^ 2 - 1)) := by
  have hx : 1 ≤ x := le_trans hy hxy
  have hle : arcosh y ≤ arcosh x :=
    (arcosh_le_arcosh (by linarith) (by linarith)).mpr hxy
  have hnn : 0 ≤ arcosh x - arcosh y := by linarith
  have hcosh : Real.cosh (arcosh x - arcosh y)
      = x * y - Real.sqrt (x ^ 2 - 1) * Real.sqrt (y ^ 2 - 1) := by
    rw [Real.cosh_sub, cosh_arcosh hx, cosh_arcosh hy, sinh_arcosh hx, sinh_arcosh hy]
  rw [← hcosh, arcosh_cosh hnn]

/-- **Doubling law for `arcosh`.** For `x ≥ 1`, `2 · arcosh x = arcosh (2x² − 1)`.

The `x = y` specialisation of `arcosh_add`, using `√(x²−1)·√(x²−1) = x² − 1`. -/
theorem two_mul_arcosh {x : ℝ} (hx : 1 ≤ x) :
    2 * arcosh x = arcosh (2 * x ^ 2 - 1) := by
  rw [two_mul, arcosh_add hx hx]
  congr 1
  rw [sqrt_sq_sub_one_mul_self hx]; ring

/-- Concrete value: `arcosh (5/4) = log 2`, since `cosh (log 2) = 5/4`.
The `cosh`-side mirror of the parent's `arsinh (3/4) = log 2`. -/
theorem arcosh_five_quarters : arcosh (5 / 4) = Real.log 2 := by
  have hsqrt : Real.sqrt ((5 / 4 : ℝ) ^ 2 - 1) = 3 / 4 := by
    rw [show ((5 / 4 : ℝ) ^ 2 - 1) = (3 / 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [arcosh_eq_log, hsqrt]; norm_num

/-- Concrete value: `arcosh (5/3) = log 3`, since `cosh (log 3) = 5/3`.
The `cosh`-side mirror of the parent's `arsinh (4/3) = log 3`. -/
theorem arcosh_five_thirds : arcosh (5 / 3) = Real.log 3 := by
  have hsqrt : Real.sqrt ((5 / 3 : ℝ) ^ 2 - 1) = 4 / 3 := by
    rw [show ((5 / 3 : ℝ) ^ 2 - 1) = (4 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [arcosh_eq_log, hsqrt]; norm_num

end ArsinhLogFormulaOQ01OQ02
