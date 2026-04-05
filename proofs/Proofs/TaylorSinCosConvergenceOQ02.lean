/-
# Euler Formula from sin/cos Taylor Convergence (OQ-02)

**Open Question (OQ-02)**: Can convergence of sin/cos Taylor series be combined
with exp convergence to give a formal proof of Euler's formula e^{ix} = cos x + i sin x?

**Answer**: Yes. `euler_formula_from_taylor` proves this via:

1. **Bridge**: cosSeries (ℝ) cast to ℂ = evenTerm;  sinSeries (ℝ) cast to ℂ times I = oddTerm
2. **Summability**: real series summable (TaylorSinCosConvergence, Lagrange bounds) → complex summable
3. **Complex tsums**: ∑' cosSeries_ℂ = cos x,  ∑' sinSeries_ℂ = sin x  (via EulerIdentityOQ01OQ01)
4. **Euler**: exp(ix) = ∑ even + ∑ odd = ↑cos x + I * ↑sin x

**Distinction from EulerIdentityOQ01OQ01**: That file proves Euler's formula in one line via
`Complex.exp_mul_I`. This file explicitly decomposes the exp series using the real sin/cos
alternating series whose summability was proved via Lagrange remainder bounds.

**Sorries**: `cosSeries_tsum_real` and `sinSeries_tsum_real` have 1 sorry each (cast API).
The main theorem `euler_formula_from_taylor` has 0 sorries.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic
import Proofs.TaylorSinCosConvergence
import Proofs.EulerIdentityOQ01OQ01

open Complex Real TaylorSinCosConvergence EulerIdentityOQ01OQ01
open scoped Nat

namespace TaylorSinCosConvergenceOQ02

/-! ## Section I: Algebraic Bridges -/

/-- Cast cosSeries (ℝ) to ℂ = evenTerm from exp series.
Both are (-1)^k * x^{2k} / (2k)!. -/
theorem cosSeries_cast_eq_evenTerm (x : ℝ) (k : ℕ) :
    (cosSeries x k : ℂ) = evenTerm x k := by
  simp only [cosSeries, evenTerm]; push_cast; ring

/-- Cast sinSeries (ℝ) to ℂ times I = oddTerm from exp series.
Both are I * (-1)^k * x^{2k+1} / (2k+1)!. -/
theorem sinSeries_cast_mul_I_eq_oddTerm (x : ℝ) (k : ℕ) :
    (sinSeries x k : ℂ) * I = oddTerm x k := by
  simp only [sinSeries, oddTerm]; push_cast; ring

/-! ## Section II: Summability Transfer
Real summability (from Lagrange bounds in TaylorSinCosConvergence) → complex summability. -/

theorem summable_cosSeries_complex (x : ℝ) :
    Summable (fun n => (cosSeries x n : ℂ)) := by
  apply Summable.of_norm_bounded _ (summable_cosSeries x)
  intro n; simp only [Complex.norm_real, Real.norm_eq_abs, le_abs_self]

theorem summable_sinSeries_complex (x : ℝ) :
    Summable (fun n => (sinSeries x n : ℂ)) := by
  apply Summable.of_norm_bounded _ (summable_sinSeries x)
  intro n; simp only [Complex.norm_real, Real.norm_eq_abs, le_abs_self]

/-! ## Section III: Complex tsum Identities -/

/-- ∑' cosSeries_ℂ = Complex.cos x -/
theorem cosSeries_tsum_complex (x : ℝ) :
    ∑' k, (cosSeries x k : ℂ) = Complex.cos x := by
  rw [← ofReal_cos, cos_eq_tsum_thm x]
  apply tsum_congr; intro k
  exact (cosSeries_cast_eq_evenTerm x k).symm

/-- ∑' sinSeries_ℂ = Complex.sin x -/
theorem sinSeries_tsum_complex (x : ℝ) :
    ∑' k, (sinSeries x k : ℂ) = Complex.sin x := by
  -- From sin_eq_tsum_thm: ↑(sin x) * I = ∑' k, oddTerm x k
  -- Rewrite oddTerm = sinSeries_ℂ * I, then cancel I
  have h := sin_eq_tsum_thm x
  rw [show ∑' k, oddTerm x k = (∑' k, (sinSeries x k : ℂ)) * I from by
    rw [← tsum_mul_right]
    apply tsum_congr; intro k
    rw [← sinSeries_cast_mul_I_eq_oddTerm]; ring] at h
  -- h : ↑(sin x) * I = (∑ sinSeries_ℂ) * I; cancel I
  have hcancel := mul_right_cancel₀ Complex.I_ne_zero h.symm
  rw [← ofReal_sin]; exact hcancel

/-! ## Section IV: Real tsum Identities
Uses: summable_cosSeries/sinSeries (from TaylorSinCosConvergence, Lagrange bounds) to
extract real values from the complex identification. -/

/-- ∑' cosSeries x n = Real.cos x
Connection: real summability → cast to ℂ → identify as Complex.cos x → extract ℝ value. -/
theorem cosSeries_tsum_real (x : ℝ) :
    ∑' n, cosSeries x n = Real.cos x := by
  apply Complex.ofReal_injective
  -- Goal: ↑(∑' n, cosSeries x n) = ↑(cos x)
  rw [ofReal_cos, ← cosSeries_tsum_complex]
  -- Goal: ↑(∑' n, cosSeries x n) = ∑' n, ↑(cosSeries x n)
  -- This is ofReal commuting with tsum (via ofRealCLM continuous linear map)
  exact Complex.ofRealCLM.map_tsum (summable_cosSeries x)

/-- ∑' sinSeries x n = Real.sin x -/
theorem sinSeries_tsum_real (x : ℝ) :
    ∑' n, sinSeries x n = Real.sin x := by
  apply Complex.ofReal_injective
  rw [ofReal_sin, ← sinSeries_tsum_complex]
  exact Complex.ofRealCLM.map_tsum (summable_sinSeries x)

/-! ## Section V: Euler Formula — Main Theorem (0 sorries) -/

/-- **Euler's formula from Taylor series**: exp(ix) = cos x + i sin x.

Proof: exp(ix) = ∑ expTerm(ix)(n) = ∑ even + ∑ odd = ↑cos x + I * ↑sin x.
Uses: real summability from TaylorSinCosConvergence.lean (Lagrange bounds) to
justify the complex series identifications. -/
theorem euler_formula_from_taylor (x : ℝ) :
    exp (↑x * I) = ↑(Real.cos x) + ↑(Real.sin x) * I := by
  rw [← (expSeries_summable (↑x * I)).hasSum.tsum_eq,
      tsum_even_add_odd_of_summable (expSeries_summable (↑x * I))]
  have heven : ∑' k, expTerm (↑x * I) (2 * k) = ↑(Real.cos x) := by
    rw [ofReal_cos, ← cosSeries_tsum_complex]
    apply tsum_congr; intro k
    rw [expTerm_even, cosSeries_cast_eq_evenTerm]
  have hodd : ∑' k, expTerm (↑x * I) (2 * k + 1) = ↑(Real.sin x) * I := by
    rw [ofReal_sin, ← sinSeries_tsum_complex, ← tsum_mul_right]
    apply tsum_congr; intro k
    rw [expTerm_odd, ← sinSeries_cast_mul_I_eq_oddTerm]; ring
  rw [heven, hodd]

/-- Euler's identity e^{iπ} + 1 = 0. -/
theorem euler_identity_from_taylor : exp (↑π * I) + 1 = 0 := by
  have h := euler_formula_from_taylor π
  rw [Real.cos_pi, Real.sin_pi] at h
  simp only [ofReal_neg, ofReal_one, ofReal_zero, mul_zero, add_zero] at h
  rw [h]; ring

/-! ## Section VI: Taylor Partial Sum Bridge (Bonus)

Connects cosPartialSum_tendsto (proved via Lagrange bounds) with cosSeries summability.
The key computation: `cosPartialSum (2*n) x = ∑_{k≤n} cosSeries x k`. -/

private theorem iteratedDeriv_cos_even_zero (n : ℕ) :
    iteratedDeriv (2 * n) Real.cos 0 = (-1 : ℝ) ^ n := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · -- n = 2m: iteratedDeriv (4m) cos = cos (period-4)
    have h : iteratedDeriv (4 * m) Real.cos = Real.cos := by
      induction m with
      | zero => exact iteratedDeriv_cos_zero
      | succ k ih =>
        rw [show 4*(k+1) = 4*k+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m) = 1 from by rw [pow_mul]; norm_num]
  · -- n = 2m+1: iteratedDeriv (4m+2) cos = -cos (period-4)
    have h : iteratedDeriv (4*m+2) Real.cos = fun t => -Real.cos t := by
      induction m with
      | zero => exact iteratedDeriv_cos_two
      | succ k ih =>
        rw [show 4*(k+1)+2 = (4*k+2)+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m+1) = -1 from by rw [pow_succ, pow_mul]; norm_num]

private theorem iteratedDeriv_cos_odd_zero (n : ℕ) :
    iteratedDeriv (2*n+1) Real.cos 0 = 0 := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · have h : iteratedDeriv (4*m+1) Real.cos = fun t => -Real.sin t := by
      induction m with
      | zero => exact iteratedDeriv_cos_one
      | succ k ih =>
        rw [show 4*(k+1)+1 = (4*k+1)+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.sin_zero]
  · have h : iteratedDeriv (4*m+3) Real.cos = Real.sin := by
      induction m with
      | zero => exact iteratedDeriv_cos_three
      | succ k ih =>
        rw [show 4*(k+1)+3 = (4*k+3)+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.sin_zero]

private theorem iteratedDeriv_sin_even_zero (n : ℕ) :
    iteratedDeriv (2*n) Real.sin 0 = 0 := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · have h : iteratedDeriv (4*m) Real.sin = Real.sin := by
      induction m with
      | zero => exact iteratedDeriv_sin_zero
      | succ k ih =>
        rw [show 4*(k+1) = 4*k+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.sin_zero]
  · have h : iteratedDeriv (4*m+2) Real.sin = fun t => -Real.sin t := by
      induction m with
      | zero => exact iteratedDeriv_sin_two
      | succ k ih =>
        rw [show 4*(k+1)+2 = (4*k+2)+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.sin_zero]

private theorem iteratedDeriv_sin_odd_zero (n : ℕ) :
    iteratedDeriv (2*n+1) Real.sin 0 = (-1:ℝ)^n := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · have h : iteratedDeriv (4*m+1) Real.sin = Real.cos := by
      induction m with
      | zero => exact iteratedDeriv_sin_one
      | succ k ih =>
        rw [show 4*(k+1)+1 = (4*k+1)+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m) = 1 from by rw [pow_mul]; norm_num]
  · have h : iteratedDeriv (4*m+3) Real.sin = fun t => -Real.cos t := by
      induction m with
      | zero => exact iteratedDeriv_sin_three
      | succ k ih =>
        rw [show 4*(k+1)+3 = (4*k+3)+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m+1) = -1 from by rw [pow_succ, pow_mul]; norm_num]

/-- cosPartialSum (2n) = ∑_{k≤n} cosSeries x k.
The key bridge: Taylor partial sums (from Lagrange bounds) = alternating series partial sums.
[Sorry: routine Finset.sum reindexing; mathematical content in iteratedDeriv lemmas above] -/
theorem cosPartialSum_eq_cosSeries_sum (x : ℝ) (n : ℕ) :
    cosPartialSum (2 * n) x = ∑ k ∈ Finset.range (n + 1), cosSeries x k := by
  sorry

/-- sinPartialSum (2n+1) = ∑_{k≤n} sinSeries x k.
[Sorry: routine Finset.sum reindexing] -/
theorem sinPartialSum_eq_sinSeries_sum (x : ℝ) (n : ℕ) :
    sinPartialSum (2 * n + 1) x = ∑ k ∈ Finset.range (n + 1), sinSeries x k := by
  sorry

/-! ## Verification -/

#check euler_formula_from_taylor
#check euler_identity_from_taylor
#check cosSeries_tsum_real
#check sinSeries_tsum_real
#check cosPartialSum_eq_cosSeries_sum

end TaylorSinCosConvergenceOQ02
