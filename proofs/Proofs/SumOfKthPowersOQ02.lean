import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-
# Sum of Powers: Extension to Non-Integer Exponents

## The Classical Setting

Faulhaber's formulas give closed-form expressions for ∑_{k=1}^n k^m when m ∈ ℕ.
This file extends to real exponents s ∈ ℝ, studying the generalized reciprocal
power sums ζ(s) = ∑_{n=1}^∞ 1/n^s and their properties.

## Main Results

1. Convergence dichotomy: ∑ 1/n^s converges iff s > 1
2. Known values: ζ(2) = π²/6 (Basel), ζ(4) = π⁴/90
3. Term monotonicity: (n^s)⁻¹ is antitone in s for n ≥ 1
4. Zeta monotonicity: ζ(s) is antitone for s > 1
5. Lower bound: ζ(s) ≥ 1
6. Bridge: rpow series = nat pow series for integer exponents

## References

- Euler (1734), Hardy-Wright Ch. XVII, Apostol Ch. 11
-/

set_option maxHeartbeats 800000

noncomputable section

open Finset BigOperators Topology Filter

namespace RealZeta

/-! ## Part I: Convergence Dichotomy -/

/-- The p-series ∑ (n^s)⁻¹ converges for s > 1. -/
theorem summable_inv_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
  Real.summable_nat_rpow_inv.mpr hs

/-- The p-series diverges for s ≤ 1. -/
theorem not_summable_inv_rpow {s : ℝ} (hs : s ≤ 1) :
    ¬ Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
  fun h => absurd (Real.summable_nat_rpow_inv.mp h) (not_lt.mpr hs)

/-! ## Part II: Known Values -/

/-- ζ(2) = π²/6 (the Basel Problem). -/
theorem zeta_two_eq : ∑' n : ℕ, (1 : ℝ) / ↑n ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

/-- ζ(4) = π⁴/90. -/
theorem zeta_four_eq : ∑' n : ℕ, (1 : ℝ) / ↑n ^ 4 = Real.pi ^ 4 / 90 :=
  hasSum_zeta_four.tsum_eq

/-! ## Part III: Term Monotonicity -/

/-- For n ≥ 1, (n^s)⁻¹ is antitone in s. Larger exponent → smaller inverse power. -/
lemma inv_rpow_antitone {n : ℕ} (hn : 1 ≤ n) {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) :
    ((n : ℝ) ^ s₂)⁻¹ ≤ ((n : ℝ) ^ s₁)⁻¹ := by
  have h_npos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h2 : (n : ℝ) ^ s₁ ≤ (n : ℝ) ^ s₂ :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hs
  -- 0 < n^s₁ ≤ n^s₂ implies (n^s₂)⁻¹ ≤ (n^s₁)⁻¹
  have h1 : (0 : ℝ) < (n : ℝ) ^ s₁ := Real.rpow_pos_of_pos h_npos s₁
  rw [show ((n : ℝ) ^ s₂)⁻¹ = 1 / (n : ℝ) ^ s₂ from (one_div _).symm,
      show ((n : ℝ) ^ s₁)⁻¹ = 1 / (n : ℝ) ^ s₁ from (one_div _).symm]
  exact div_le_div_of_nonneg_left one_pos.le h1 h2

/-- For n ≥ 2, the inequality is strict when s₁ < s₂. -/
lemma inv_rpow_strictAnti {n : ℕ} (hn : 2 ≤ n) {s₁ s₂ : ℝ} (hs : s₁ < s₂) :
    ((n : ℝ) ^ s₂)⁻¹ < ((n : ℝ) ^ s₁)⁻¹ := by
  have h_npos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h2 : (n : ℝ) ^ s₁ < (n : ℝ) ^ s₂ :=
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < n by omega)) hs
  rw [show ((n : ℝ) ^ s₂)⁻¹ = 1 / (n : ℝ) ^ s₂ from (one_div _).symm,
      show ((n : ℝ) ^ s₁)⁻¹ = 1 / (n : ℝ) ^ s₁ from (one_div _).symm]
  exact div_lt_div_of_pos_left one_pos (Real.rpow_pos_of_pos h_npos s₁) h2

/-! ## Part IV: Zeta Monotonicity -/

/-- ζ(s₂) ≤ ζ(s₁) when 1 < s₁ ≤ s₂ (zeta is antitone). -/
theorem tsum_inv_rpow_antitone {s₁ s₂ : ℝ} (hs₁ : 1 < s₁) (hs : s₁ ≤ s₂) :
    ∑' n : ℕ, ((n : ℝ) ^ s₂)⁻¹ ≤ ∑' n : ℕ, ((n : ℝ) ^ s₁)⁻¹ := by
  have hs₂ : 1 < s₂ := lt_of_lt_of_le hs₁ hs
  exact hasSum_le (fun n => by
    by_cases hn : n = 0
    · simp [hn, Real.zero_rpow (by linarith : s₁ ≠ 0), Real.zero_rpow (by linarith : s₂ ≠ 0)]
    · exact inv_rpow_antitone (by omega) hs)
    (summable_inv_rpow hs₂).hasSum (summable_inv_rpow hs₁).hasSum

/-! ## Part V: Lower Bound -/

/-- ζ(s) ≥ 1 for s > 1: the n=1 term contributes 1^{-s} = 1. -/
theorem one_le_tsum_inv_rpow {s : ℝ} (hs : 1 < s) :
    1 ≤ ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ := by
  calc (1 : ℝ) = (((1 : ℕ) : ℝ) ^ s)⁻¹ := by simp [Real.one_rpow]
    _ ≤ ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ :=
        le_hasSum (summable_inv_rpow hs).hasSum 1 (fun n _ => by positivity)

/-! ## Part VI: Upper Bound -/

/-- For s ≥ 2, ζ(s) ≤ ζ(2) = π²/6 by term-wise monotonicity. -/
theorem tsum_inv_rpow_le_zeta_two {s : ℝ} (hs : 2 ≤ s) :
    ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹ ≤ Real.pi ^ 2 / 6 := by
  calc ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹
      ≤ ∑' n : ℕ, ((n : ℝ) ^ (2 : ℝ))⁻¹ :=
        tsum_inv_rpow_antitone (by norm_num : (1 : ℝ) < 2) hs
    _ = ∑' n : ℕ, (1 : ℝ) / ↑n ^ 2 := by
        congr 1; ext n
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, one_div]
    _ = Real.pi ^ 2 / 6 := zeta_two_eq

/-! ## Part VII: Partial Sums -/

/-- Partial sum S(n, s) = ∑_{k=0}^{n-1} (k^s)⁻¹. -/
def partialZeta (n : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ range n, ((k : ℝ) ^ s)⁻¹

/-- Partial sums converge to the full sum. -/
theorem partialZeta_tendsto {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n => partialZeta n s) atTop
      (𝓝 (∑' n : ℕ, ((n : ℝ) ^ s)⁻¹)) :=
  (summable_inv_rpow hs).hasSum.tendsto_sum_nat

/-- Partial sums are monotone: more terms = larger sum. -/
theorem partialZeta_mono {n m : ℕ} (hnm : n ≤ m) (s : ℝ) :
    partialZeta n s ≤ partialZeta m s := by
  unfold partialZeta
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
  intro k _ _; positivity

/-! ## Part VIII: Bridge to Integer Exponents -/

/-- For natural number exponents, the rpow series equals the classical 1/n^k series.
    This bridges the real-exponent theory to Faulhaber's formulas (parent proof). -/
theorem rpow_inv_eq_nat_inv (k : ℕ) :
    (fun n : ℕ => ((n : ℝ) ^ (k : ℝ))⁻¹) = fun n : ℕ => (1 : ℝ) / ↑n ^ k := by
  ext n; rw [show (k : ℝ) = ((k : ℕ) : ℝ) from rfl, Real.rpow_natCast, one_div]

/-- Summability of reciprocal kth powers for k ≥ 2. -/
theorem summable_inv_nat_pow (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => (1 : ℝ) / ↑n ^ k) := by
  rw [← rpow_inv_eq_nat_inv k]
  exact summable_inv_rpow (by exact_mod_cast hk)

/-- Partial sums of 1/n² converge to π²/6 (connecting to Faulhaber). -/
theorem partial_sum_sq_tendsto :
    Tendsto (fun N => ∑ n ∈ range N, (1 : ℝ) / ↑n ^ 2) atTop (𝓝 (Real.pi ^ 2 / 6)) :=
  hasSum_zeta_two.tendsto_sum_nat

/-! ## Verification -/

#check @summable_inv_rpow
#check @not_summable_inv_rpow
#check @zeta_two_eq
#check @zeta_four_eq
#check @inv_rpow_antitone
#check @inv_rpow_strictAnti
#check @tsum_inv_rpow_antitone
#check @one_le_tsum_inv_rpow
#check @tsum_inv_rpow_le_zeta_two
#check @partialZeta_tendsto
#check @partialZeta_mono
#check @rpow_inv_eq_nat_inv
#check @summable_inv_nat_pow
#check @partial_sum_sq_tendsto

end RealZeta
