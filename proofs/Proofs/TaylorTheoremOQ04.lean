/-
# Taylor Series Convergence of sin and cos via the Uniform Derivative Bound

Parent: `proofs/Proofs/TaylorTheorem.lean` (Taylor's theorem with Lagrange
remainder). This child (`taylor-theorem-oq-04`) proves that the Taylor
polynomials of `sin` and `cos` converge to the functions at every real point,
using a route distinct from the sibling children:

* oq-02 uses abstract formal power series;
* oq-03 uses `NormedSpace.exp` summability;
* **this file** uses the *uniform derivative bound* `|fⁿ| ≤ 1`.

Because every iterated derivative of `sin`/`cos` is bounded by `1`, the uniform
Taylor remainder bound (`taylor_mean_remainder_bound`) gives

  `|f x - Tₙ(x)| ≤ |x|^{n+1} / n!  →  0`,

the classic "entire function with uniformly bounded derivatives has an
everywhere-convergent Taylor series" argument.

All results are verified (0 axioms): they assemble named Mathlib lemmas
(`taylor_mean_remainder_bound`, `iteratedDerivWithin_sin_Icc`,
`abs_iteratedDeriv_sin_le_one`, `Real.summable_pow_div_factorial`).

References:
* Mathlib `Analysis/Calculus/Taylor.lean` — `taylor_mean_remainder_bound`.
* Mathlib `Analysis/SpecialFunctions/Trigonometric/Deriv.lean` —
  `abs_iteratedDeriv_sin_le_one`, `iteratedDerivWithin_sin_Icc`.
* Mathlib `Analysis/SpecificLimits/Normed.lean` —
  `Real.summable_pow_div_factorial`.
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Proofs.TaylorTheoremOQ04

open Set Filter Topology
open scoped Nat

/-- **Uniform Taylor remainder bound for `sin`.** On `[0, x]` (with `x > 0`),
the `n`-th Taylor polynomial of `sin` at `0` approximates `sin x` with error at
most `x^{n+1}/n!`. The proof feeds the uniform derivative bound
`|sin⁽ⁿ⁺¹⁾| ≤ 1` into `taylor_mean_remainder_bound` with `C = 1`. -/
theorem sin_taylor_remainder_le (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.sin x - taylorWithinEval Real.sin n (Icc 0 x) 0 x| ≤ x ^ (n + 1) / n ! := by
  have hbound : ∀ y ∈ Icc (0 : ℝ) x,
      ‖iteratedDerivWithin (n + 1) Real.sin (Icc 0 x) y‖ ≤ 1 := by
    intro y hy
    rw [Real.iteratedDerivWithin_sin_Icc _ hx hy, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_sin_le_one _ y
  have h := taylor_mean_remainder_bound (f := Real.sin) (a := 0) (b := x) (C := 1)
    hx.le (Real.contDiff_sin.of_le le_top).contDiffOn (right_mem_Icc.2 hx.le) hbound
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.le] using h

/-- **Uniform Taylor remainder bound for `cos`.** Same statement and proof as
`sin_taylor_remainder_le`, using `|cos⁽ⁿ⁺¹⁾| ≤ 1`. -/
theorem cos_taylor_remainder_le (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x| ≤ x ^ (n + 1) / n ! := by
  have hbound : ∀ y ∈ Icc (0 : ℝ) x,
      ‖iteratedDerivWithin (n + 1) Real.cos (Icc 0 x) y‖ ≤ 1 := by
    intro y hy
    rw [Real.iteratedDerivWithin_cos_Icc _ hx hy, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_cos_le_one _ y
  have h := taylor_mean_remainder_bound (f := Real.cos) (a := 0) (b := x) (C := 1)
    hx.le (Real.contDiff_cos.of_le le_top).contDiffOn (right_mem_Icc.2 hx.le) hbound
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.le] using h

/-- The remainder bound `x^{n+1}/n! → 0` as `n → ∞`, for fixed `x`. Factor
`x^{n+1}/n! = x · (x^n/n!)`; the base sequence `x^n/n!` tends to `0` because it
is the general term of the (summable) exponential series
(`Real.summable_pow_div_factorial`). -/
theorem pow_succ_div_factorial_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => x ^ (n + 1) / n !) atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ => x ^ n / n !) atTop (nhds 0) :=
    (Real.summable_pow_div_factorial x).tendsto_atTop_zero
  have hmul : Tendsto (fun n : ℕ => x * (x ^ n / n !)) atTop (nhds (x * 0)) :=
    hbase.const_mul x
  rw [mul_zero] at hmul
  refine hmul.congr (fun n => ?_)
  rw [pow_succ]; ring

/-- **Taylor series of `sin` converges.** For every `x > 0`, the remainder
`sin x - Tₙ(x)` tends to `0`, so the Taylor series of `sin` converges to `sin`
at `x`. Squeeze the remainder between `0` and `x^{n+1}/n! → 0`. -/
theorem sin_taylor_remainder_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => Real.sin x - taylorWithinEval Real.sin n (Icc 0 x) 0 x)
      atTop (nhds 0) := by
  refine squeeze_zero_norm (fun n => ?_) (pow_succ_div_factorial_tendsto_zero x)
  rw [Real.norm_eq_abs]
  exact sin_taylor_remainder_le x hx n

/-- **Taylor series of `cos` converges.** For every `x > 0`, the remainder
`cos x - Tₙ(x)` tends to `0`. -/
theorem cos_taylor_remainder_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x)
      atTop (nhds 0) := by
  refine squeeze_zero_norm (fun n => ?_) (pow_succ_div_factorial_tendsto_zero x)
  rw [Real.norm_eq_abs]
  exact cos_taylor_remainder_le x hx n

end Proofs.TaylorTheoremOQ04
