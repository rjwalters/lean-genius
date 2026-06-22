/-
# Binet's closest-integer formula: fib(n) = round(φⁿ/√5) (GCD OQ-01-OQ-01)

The parent entry **gcd-algorithm-oq-01** ("Average-Case Complexity of the
Euclidean Algorithm") formalizes Lamé's worst-case theorem — the Euclidean
algorithm on consecutive Fibonacci numbers takes the most steps — and asks, among
its open questions, to formalize **the golden-ratio identity**
`fib(n) = ⌊φⁿ/√5 + ½⌋`, the closest-integer form of Binet's formula, which is the
quantitative engine behind the Lamé step bound (`b ≥ fib(steps+1)`, with
`fib(n) ≈ φⁿ/√5` growing geometrically).

This file proves it, axiom-free, from Mathlib's `Real.coe_fib_eq`
(`fib n = (φⁿ − ψⁿ)/√5`) and the bound `|ψ| < 1`:

  * `abs_fib_sub_binet` — `|fib(n) − φⁿ/√5| < ½` for all `n`, since the difference
    is exactly `−ψⁿ/√5` and `|ψⁿ|/√5 ≤ 1/√5 < ½`;
  * `fib_eq_round_binet` — hence `round(φⁿ/√5) = fib(n)`: the Fibonacci numbers are
    exactly the nearest integers to the geometric sequence `φⁿ/√5`;
  * `fib_lt_goldenRatio_pow_div_add_half` / `goldenRatio_pow_div_sub_half_lt_fib` —
    the explicit sandwich `φⁿ/√5 − ½ < fib(n) < φⁿ/√5 + ½`.

This is the precise sense in which the Euclidean worst case grows geometrically:
`fib(n)` tracks `φⁿ/√5` to within half a unit, so the `n`-step worst case needs
inputs of size `≈ φⁿ`, i.e. `n ≈ log_φ(√5·b)` steps — the Lamé bound.

Zero axioms; imports only Mathlib.
-/
import Mathlib

open scoped goldenRatio
open Real

namespace GcdAlgorithmOQ01OQ01

/-- `√5 > 2` (since `5 > 4`). -/
theorem two_lt_sqrt_five : (2 : ℝ) < √5 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

/-- The golden conjugate `ψ = (1−√5)/2` has `|ψ| < 1`. -/
theorem abs_goldenConj_lt_one : |ψ| < 1 := by
  rw [abs_of_neg goldenConj_neg]; linarith [neg_one_lt_goldenConj]

/-- **The Binet error is less than ½.** For every `n`, `fib(n)` differs from
`φⁿ/√5` by less than `½`, because the difference is exactly `−ψⁿ/√5` and
`|ψⁿ|/√5 ≤ 1/√5 < ½`. -/
theorem abs_fib_sub_binet (n : ℕ) : |(Nat.fib n : ℝ) - φ ^ n / √5| < 1 / 2 := by
  have h5 : (0 : ℝ) < √5 := by linarith [two_lt_sqrt_five]
  have heq : (Nat.fib n : ℝ) - φ ^ n / √5 = -ψ ^ n / √5 := by
    rw [Real.coe_fib_eq n]; field_simp; ring
  rw [heq, abs_div, abs_neg, abs_pow, abs_of_pos h5, div_lt_iff₀ h5]
  have hpsi : |ψ| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) abs_goldenConj_lt_one.le
  nlinarith [hpsi, two_lt_sqrt_five]

/-- **Binet's closest-integer formula.** The `n`-th Fibonacci number is the nearest
integer to `φⁿ/√5`:  `round(φⁿ/√5) = fib(n)`. -/
theorem fib_eq_round_binet (n : ℕ) : round (φ ^ n / √5) = (Nat.fib n : ℤ) := by
  have habs := abs_fib_sub_binet n
  rw [abs_lt] at habs
  rw [round_eq, Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · push_cast; linarith [habs.2]
  · push_cast; linarith [habs.1]

/-- The upper half of the sandwich: `fib(n) < φⁿ/√5 + ½`. -/
theorem fib_lt_goldenRatio_pow_div_add_half (n : ℕ) :
    (Nat.fib n : ℝ) < φ ^ n / √5 + 1 / 2 := by
  have := (abs_lt.mp (abs_fib_sub_binet n)).2; linarith

/-- The lower half of the sandwich: `φⁿ/√5 − ½ < fib(n)`. -/
theorem goldenRatio_pow_div_sub_half_lt_fib (n : ℕ) :
    φ ^ n / √5 - 1 / 2 < (Nat.fib n : ℝ) := by
  have := (abs_lt.mp (abs_fib_sub_binet n)).1; linarith

end GcdAlgorithmOQ01OQ01
