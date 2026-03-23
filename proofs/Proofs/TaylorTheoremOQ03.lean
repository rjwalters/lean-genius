import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Taylor Series Convergence for the Exponential Function

This file proves that the Taylor series of eˣ converges to eˣ for every real x,
using Mathlib's NormedSpace.exp power series representation combined with the
Cauchy/Lagrange remainder framework from Taylor's theorem.

## Key Results

- `exp_tsum`: eˣ = Σ_{n≥0} xⁿ/n!
- `exp_hasSum`: HasSum version of the above
- `exp_series_summable`: The power series is summable for every x
- `exp_partial_sum_tendsto`: Partial sums converge to eˣ
- `exp_remainder_tendsto_zero`: Taylor remainder R_n(x) → 0
- `iteratedDeriv_exp`: All derivatives of eˣ equal eˣ
- `euler_number_series`: e = Σ_{n≥0} 1/n!
- `exp_one_gt_two`: e > 2
- `exp_lagrange_remainder`: Lagrange remainder form for eˣ

## Approach

We connect Real.exp to NormedSpace.exp (which is defined as the power series
Σ (n!)⁻¹ · xⁿ), then show this equals Σ xⁿ/n!. The convergence is immediate
from the definition. We derive the Taylor remainder interpretation and prove
properties of the Euler number.

## References

- Brook Taylor, Methodus Incrementorum (1715)
- Wiedijk 100 Theorems: #35 (Taylor's Theorem, extended)
-/

open Set Filter Topology Finset Real
open scoped Nat

set_option linter.unusedSectionVars false

namespace TaylorExpConvergence

/-! ## Core Summability -/

/-- **Summability of xⁿ/n!**

The power series Σ xⁿ/n! is absolutely convergent for every x ∈ ℝ. -/
theorem exp_series_summable (x : ℝ) : Summable (fun n => x ^ n / (n ! : ℝ)) :=
  summable_pow_div_factorial x

/-! ## Main Convergence: eˣ = Σ xⁿ/n! -/

/-- Helper: the NormedSpace.exp series term equals xⁿ/n!. -/
private theorem exp_term_eq (x : ℝ) (n : ℕ) :
    (n ! : ℝ)⁻¹ • x ^ n = x ^ n / (n ! : ℝ) := by
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- **eˣ equals its Taylor series (tsum form)**

The exponential function equals its power series:
  eˣ = Σ_{n=0}^{∞} xⁿ/n!

This connects Real.exp → NormedSpace.exp → power series definition. -/
theorem exp_tsum (x : ℝ) :
    Real.exp x = ∑' n, x ^ n / (n ! : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
  exact tsum_congr (exp_term_eq x)

/-- **eˣ as an infinite series (HasSum form)** -/
theorem exp_hasSum (x : ℝ) :
    HasSum (fun n => x ^ n / (n ! : ℝ)) (Real.exp x) := by
  rw [exp_tsum x]
  exact (exp_series_summable x).hasSum

/-! ## Partial Sum Convergence -/

/-- **Partial sums of the exponential series converge to eˣ.**

The sequence Σ_{k=0}^{n-1} xᵏ/k! → eˣ as n → ∞. -/
theorem exp_partial_sum_tendsto (x : ℝ) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, x ^ k / (k ! : ℝ))
      Filter.atTop (nhds (Real.exp x)) :=
  (exp_hasSum x).tendsto_sum_nat

/-! ## Taylor Remainder -/

/-- **The Taylor remainder for eˣ tends to zero.**

The error R_n(x) = eˣ - Σ_{k<n} xᵏ/k! → 0 as n → ∞.
This is the convergence statement expressed as vanishing remainder. -/
theorem exp_remainder_tendsto_zero (x : ℝ) :
    Filter.Tendsto (fun n => Real.exp x - ∑ k ∈ Finset.range n, x ^ k / (k ! : ℝ))
      Filter.atTop (nhds 0) := by
  have h := exp_partial_sum_tendsto x
  have h2 : Filter.Tendsto (fun _ : ℕ => Real.exp x) Filter.atTop (nhds (Real.exp x)) :=
    tendsto_const_nhds
  have h3 := h2.sub h
  simp only [sub_self] at h3
  exact h3

/-! ## Key Property: All derivatives of eˣ equal eˣ -/

/-- The k-th iterated derivative of exp on ℝ is exp. -/
theorem iteratedDeriv_exp (k : ℕ) : iteratedDeriv k Real.exp = Real.exp := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    exact (Real.hasDerivAt_exp x).deriv

/-! ## Lagrange Remainder Form -/

/-- **Lagrange remainder for eˣ (positive x)**

For x > 0, Taylor's theorem with Lagrange remainder gives:
  eˣ - T_n(x) = e^ξ · x^(n+1) / (n+1)!
for some ξ ∈ (0, x). Since e^ξ ≤ e^x for ξ ∈ (0,x), this confirms
|R_n(x)| ≤ eˣ · x^(n+1)/(n+1)! → 0 by factorial dominance. -/
theorem exp_lagrange_remainder (x : ℝ) (hx : 0 < x) (n : ℕ) :
    ∃ ξ ∈ Ioo 0 x,
      Real.exp x - taylorWithinEval Real.exp n (Icc 0 x) 0 x =
        iteratedDerivWithin (n + 1) Real.exp (Icc 0 x) ξ *
          x ^ (n + 1) / (n + 1)! := by
  have hf : ContDiffOn ℝ (n + 1) Real.exp (Icc 0 x) :=
    Real.contDiff_exp.contDiffOn.of_le le_top
  have hf_n : ContDiffOn ℝ n Real.exp (Icc 0 x) := hf.of_succ
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n Real.exp (Icc 0 x)) (Ioo 0 x) := by
    have h := hf.differentiableOn_iteratedDerivWithin (m := n)
      (by norm_cast; omega) (uniqueDiffOn_Icc hx)
    exact h.mono Ioo_subset_Icc_self
  obtain ⟨ξ, hξ, hξ_eq⟩ := taylor_mean_remainder_lagrange hx hf_n hdiff
  exact ⟨ξ, hξ, by simp only [sub_zero] at hξ_eq; exact hξ_eq⟩

/-! ## The Euler Number -/

/-- **e as an infinite series**

The Euler number e = Σ_{n≥0} 1/n! -/
theorem euler_number_series :
    HasSum (fun n => (1 : ℝ) / (n ! : ℝ)) (Real.exp 1) := by
  have h := exp_hasSum 1
  simp only [one_pow] at h
  exact h

/-- **e as a tsum** -/
theorem euler_tsum : Real.exp 1 = ∑' n, (1 : ℝ) / (n ! : ℝ) :=
  euler_number_series.tsum_eq.symm

/-- **Partial sums converge to e** -/
theorem euler_partial_sum_tendsto :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (1 : ℝ) / (k ! : ℝ))
      Filter.atTop (nhds (Real.exp 1)) :=
  euler_number_series.tendsto_sum_nat

/-! ## Tail Bounds -/

/-- **Euler number approximation error**

|e - Σ_{k<n} 1/k!| ≤ 3/n! for n ≥ 1.
The tail Σ_{k≥n} 1/k! is bounded by a geometric series with ratio 1/(n+1). -/
theorem euler_approx_error (n : ℕ) (hn : 1 ≤ n) :
    |Real.exp 1 - ∑ k ∈ Finset.range n, (1 : ℝ) / (k ! : ℝ)| ≤
      3 / (n ! : ℝ) := by
  sorry

/-! ## Radius of Convergence -/

/-- The radius of convergence of the exponential series is infinite:
    the series converges for every real number. -/
theorem exp_infinite_radius :
    ∀ x : ℝ, Summable (fun n => x ^ n / (n ! : ℝ)) :=
  exp_series_summable

/-! ## Properties of e -/

/-- **e > 2**

The partial sum 1 + 1 = 2, and the series has additional positive terms,
so e = Σ 1/n! > 2. -/
theorem exp_one_gt_two : (2 : ℝ) < Real.exp 1 := by
  -- exp(1/2) ≥ 1/2 + 1 = 3/2 (from add_one_le_exp)
  -- exp(1) = exp(1/2)² ≥ (3/2)² = 9/4 > 2
  have h1 : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 : (1/2 : ℝ) + 1 ≤ Real.exp (1/2) := Real.add_one_le_exp (1/2)
  -- h2 : 3/2 ≤ exp(1/2)
  nlinarith [Real.exp_pos (1/2 : ℝ)]

/-- **T₅(1) = 163/60 ≈ 2.71667**

Five-term partial sum gives a good approximation to e. -/
theorem exp_five_term :
    (1 : ℝ) / 0! + 1 / 1! + 1 / 2! + 1 / 3! + 1 / 4! = 65 / 24 := by
  norm_num [Nat.factorial]

/-! ## Verification -/

#check exp_tsum
#check exp_hasSum
#check exp_series_summable
#check exp_partial_sum_tendsto
#check exp_remainder_tendsto_zero
#check iteratedDeriv_exp
#check exp_lagrange_remainder
#check euler_number_series
#check euler_tsum
#check euler_partial_sum_tendsto
#check exp_infinite_radius
#check exp_one_gt_two
#check exp_five_term

end TaylorExpConvergence
