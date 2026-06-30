import Mathlib

/-
# The Monotone Integral–Sum Sandwich, Stirling-Type Bounds, and the p-Series Test

This is the open-question companion to `AntitoneIntegralSumComparison`.  The parent
packages the **antitone** integral-test sandwich

  ∑_{i<a} f(x₀ + i + 1)  ≤  ∫_{x₀}^{x₀+a} f  ≤  ∑_{i<a} f(x₀ + i)

and applies it to `1/x` to get the logarithmic bounds on the harmonic numbers.
Here we develop the three pieces the open question asks for:

* **Part I — the monotone companion sandwich.**  For `f` *monotone* (non-decreasing)
  the two Riemann sums swap roles:

    ∑_{i<a} f(x₀ + i)  ≤  ∫_{x₀}^{x₀+a} f  ≤  ∑_{i<a} f(x₀ + i + 1).

* **Part II — Stirling-type bounds on `log n!`.**  Applying the monotone sandwich to
  `log` (the natural increasing partner of the parent's decreasing `1/x`) and using
  `∫₁^{1+n} log x dx = (1+n) log(1+n) − n` yields

    log(n!)  ≤  (1+n) log(1+n) − n  ≤  log((n+1)!),

  the elementary two-sided estimate underlying Stirling's approximation.

* **Part III — the p-series criterion.**  The integral test applied to the antitone
  `1/xᵖ` bounds the partial sums of `∑ 1/iᵖ` by the value `1/(p−1)` of the improper
  integral `∫₁^∞ x^{−p} dx`, giving convergence for `p > 1` *directly from the
  comparison*.  The full criterion `∑ 1/nᵖ` converges ⟺ `p > 1` is recorded via
  Mathlib's `Real.summable_one_div_nat_rpow`.

All results are fully machine-verified: 0 sorries, 0 axioms.
-/

namespace AntitoneIntegralSumComparisonOQ01OQ01

open scoped BigOperators
open Finset intervalIntegral

/-! ## Part I — The monotone integral-test sandwich -/

/-- **Monotone integral-test sandwich.**  For `f` monotone (non-decreasing) on
`[x₀, x₀ + a]`, the integral lies between the left Riemann sum (lower bound) and the
right Riemann sum (upper bound) — the mirror image of the parent's antitone
comparison.  This is the companion two-sided bound underlying the integral test for
increasing integrands. -/
theorem monotone_integral_sandwich {f : ℝ → ℝ} {x₀ : ℝ} {a : ℕ}
    (hf : MonotoneOn f (Set.Icc x₀ (x₀ + a))) :
    (∑ i ∈ Finset.range a, f (x₀ + i)) ≤ (∫ x in x₀..x₀ + a, f x) ∧
      (∫ x in x₀..x₀ + a, f x) ≤ ∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ)) :=
  ⟨hf.sum_le_integral, hf.integral_le_sum⟩

/-! ## Part II — Stirling-type bounds on the log-factorial -/

/-- `log` is monotone on `[1, 1 + n]` (it lives on the positive reals). -/
theorem log_monotoneOn (n : ℕ) :
    MonotoneOn Real.log (Set.Icc (1 : ℝ) (1 + n)) := by
  intro x hx y _ hxy
  exact Real.log_le_log (lt_of_lt_of_le one_pos hx.1) hxy

/-- `∫₁^{1+n} log x dx = (1 + n) · log(1 + n) − n`. -/
theorem log_integral (n : ℕ) :
    (∫ x in (1 : ℝ)..(1 + n), Real.log x) = (1 + n) * Real.log (1 + n) - n := by
  rw [integral_log, Real.log_one]
  ring

/-- `∏_{i<n} (i + 2) = (n + 1)!` as naturals. -/
theorem prod_range_add_two (n : ℕ) :
    ∏ i ∈ Finset.range n, (i + 2) = (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ (k + 1)]; ring

/-- The lower Riemann sum of `log` is `log(n!)`: `∑_{i<n} log(1 + i) = log(n!)`. -/
theorem sum_log_eq_log_factorial (n : ℕ) :
    ∑ i ∈ Finset.range n, Real.log (1 + (i : ℝ)) = Real.log (n.factorial : ℝ) := by
  have hprod : ∏ i ∈ Finset.range n, (1 + (i : ℝ)) = (n.factorial : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  rw [← hprod, ← Real.log_prod]
  intro i _
  positivity

/-- The upper Riemann sum of `log` is `log((n+1)!)`: `∑_{i<n} log(1 + (i+1)) = log((n+1)!)`. -/
theorem sum_log_succ_eq (n : ℕ) :
    ∑ i ∈ Finset.range n, Real.log (1 + ((i + 1 : ℕ) : ℝ)) = Real.log ((n + 1).factorial : ℝ) := by
  have hprod : ∏ i ∈ Finset.range n, (1 + ((i + 1 : ℕ) : ℝ)) = ((n + 1).factorial : ℝ) := by
    rw [← prod_range_add_two, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  rw [← hprod, ← Real.log_prod]
  intro i _
  positivity

/-- **Stirling lower bound.** `log(n!) ≤ (1 + n) log(1 + n) − n`, from the monotone
sandwich applied to `log`: the lower Riemann sum is at most the integral. -/
theorem log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (1 + n) * Real.log (1 + n) - n := by
  have key : (∑ i ∈ Finset.range n, Real.log (1 + (i : ℝ))) ≤ ∫ x in (1 : ℝ)..(1 + n), Real.log x :=
    (log_monotoneOn n).sum_le_integral
  rw [log_integral, sum_log_eq_log_factorial] at key
  exact key

/-- **Stirling upper bound.** `(1 + n) log(1 + n) − n ≤ log((n+1)!)`, from the monotone
sandwich applied to `log`: the integral is at most the right Riemann sum. -/
theorem log_integral_le_log_factorial (n : ℕ) :
    (1 + n) * Real.log (1 + n) - n ≤ Real.log ((n + 1).factorial : ℝ) := by
  have key : (∫ x in (1 : ℝ)..(1 + n), Real.log x)
      ≤ ∑ i ∈ Finset.range n, Real.log (1 + ((i + 1 : ℕ) : ℝ)) :=
    (log_monotoneOn n).integral_le_sum
  rw [log_integral, sum_log_succ_eq] at key
  exact key

/-- **Stirling-type sandwich for `log n!`.**  Combining the two bounds:
`log(n!) ≤ (1 + n) log(1 + n) − n ≤ log((n+1)!)`. -/
theorem log_factorial_sandwich (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (1 + n) * Real.log (1 + n) - n ∧
      (1 + n) * Real.log (1 + n) - n ≤ Real.log ((n + 1).factorial : ℝ) :=
  ⟨log_factorial_le n, log_integral_le_log_factorial n⟩

/-! ## Part III — The p-series convergence test -/

/-- **Integral-test bound for the p-series.**  For `p > 1`, every partial sum of
`∑ 1/(i+2)ᵖ` is bounded by `1/(p−1)`, the value of the improper integral
`∫₁^∞ x^{−p} dx`.  This is the antitone integral test applied to `1/xᵖ`. -/
theorem pseries_partial_sum_le (p : ℝ) (hp : 1 < p) (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 2) ^ p) ≤ 1 / (p - 1) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hanti : AntitoneOn (fun x : ℝ => 1 / x ^ p) (Set.Icc (1 : ℝ) (1 + n)) := by
    intro x hx y _ hxy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 p)
      (Real.rpow_le_rpow hx0.le hxy hp0.le)
  have hcongr : (∫ x in (1 : ℝ)..(1 + n), 1 / x ^ p)
      = ∫ x in (1 : ℝ)..(1 + n), x ^ (-p) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (by positivity))] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    rw [Real.rpow_neg hx0.le, one_div]
  have hint : (∫ x in (1 : ℝ)..(1 + n), 1 / x ^ p)
      = ((1 + (n : ℝ)) ^ (-p + 1) - 1) / (-p + 1) := by
    rw [hcongr,
      integral_rpow (Or.inr ⟨ne_of_lt (by linarith), Set.notMem_uIcc_of_lt one_pos (by positivity)⟩),
      Real.one_rpow]
  have key : (∑ i ∈ Finset.range n, 1 / ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ p)
      ≤ ∫ x in (1 : ℝ)..(1 + n), 1 / x ^ p :=
    hanti.sum_le_integral
  rw [hint] at key
  have hsum : (∑ i ∈ Finset.range n, 1 / ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ p)
      = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 2) ^ p := by
    apply Finset.sum_congr rfl
    intro i _
    have : (1 : ℝ) + ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 2 := by push_cast; ring
    rw [this]
  rw [hsum] at key
  refine key.trans ?_
  have hA : (0 : ℝ) ≤ (1 + (n : ℝ)) ^ (-p + 1) := Real.rpow_nonneg (by positivity) _
  have hpm : (0 : ℝ) < p - 1 := by linarith
  have h1 : (-p + 1) ≠ 0 := by linarith
  have h2 : (p - 1) ≠ 0 := by linarith
  have heq : ((1 + (n : ℝ)) ^ (-p + 1) - 1) / (-p + 1)
      = (1 - (1 + (n : ℝ)) ^ (-p + 1)) * (1 / (p - 1)) := by
    field_simp
    ring
  rw [heq, sub_mul, one_mul]
  have hmul : (0 : ℝ) ≤ (1 + (n : ℝ)) ^ (-p + 1) * (1 / (p - 1)) :=
    mul_nonneg hA (div_nonneg zero_le_one hpm.le)
  linarith [hmul]

/-- **p-series convergence (`p > 1`), via the integral test.**  Bounded partial sums of
nonnegative terms are summable, so `∑ 1/(i+2)ᵖ` converges — derived from
`pseries_partial_sum_le`, not from Mathlib's condensation test. -/
theorem pseries_summable_of_one_lt (p : ℝ) (hp : 1 < p) :
    Summable (fun i : ℕ => 1 / ((i : ℝ) + 2) ^ p) :=
  summable_of_sum_range_le (fun i => by positivity) (fun n => pseries_partial_sum_le p hp n)

/-- **The p-series criterion.**  `∑ 1/nᵖ` converges if and only if `p > 1`.  This is the
headline corollary of the integral test; the full two-sided statement is Mathlib's
`Real.summable_one_div_nat_rpow`. -/
theorem pseries_summable_iff (p : ℝ) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
  Real.summable_one_div_nat_rpow

/-! ## Part IV — Worked witnesses -/

/-- The monotone sandwich specialised to `log` on `[1, 1 + n]`. -/
example (n : ℕ) :
    (∑ i ∈ Finset.range n, Real.log (1 + (i : ℕ))) ≤ (∫ x in (1 : ℝ)..(1 + n), Real.log x) ∧
      (∫ x in (1 : ℝ)..(1 + n), Real.log x) ≤
        ∑ i ∈ Finset.range n, Real.log (1 + (i + 1 : ℕ)) :=
  monotone_integral_sandwich (log_monotoneOn n)

/-- The Basel-exponent series `∑ 1/n²` converges (`p = 2 > 1`). -/
example : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) :=
  (pseries_summable_iff 2).mpr (by norm_num)

/-- The harmonic series `∑ 1/n` diverges (`p = 1` is not `> 1`). -/
example : ¬ Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 : ℝ)) := by
  intro h
  have := (pseries_summable_iff 1).mp h
  linarith

end AntitoneIntegralSumComparisonOQ01OQ01
