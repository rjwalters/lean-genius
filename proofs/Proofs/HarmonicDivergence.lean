import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Divergence of the Harmonic Series

## What This Proves
The harmonic series ∑_{n=1}^∞ 1/n diverges—its partial sums grow without bound.
This is one of the most surprising results in analysis: even though the terms
1, 1/2, 1/3, 1/4, ... approach zero, their sum is infinite.

## Approach
- **Foundation (from Mathlib):** We use `Real.not_summable_one_div_natCast` which
  proves the harmonic series is not summable, and `Real.tendsto_sum_range_one_div_nat_succ_atTop`
  which shows the partial sums tend to infinity.
- **Classical Proof (Oresme, ~1350):** Group terms: 1/3 + 1/4 > 1/2, 1/5 + ... + 1/8 > 1/2, etc.
  Each group of 2^k terms sums to more than 1/2, so the series diverges.
- **Proof Techniques Demonstrated:** Comparison tests, grouping arguments,
  properties of summable series.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Real.not_summable_one_div_natCast` : The harmonic series is not summable
- `Real.tendsto_sum_range_one_div_nat_succ_atTop` : Partial sums → ∞
- `Summable` : Predicate for convergent series

## Historical Note
Nicole Oresme (~1350) gave the first proof of harmonic divergence using the
grouping argument. This was one of the earliest uses of infinite series in
mathematics. The result was independently rediscovered by Pietro Mengoli (1647)
and Johann Bernoulli (1689).
-/

namespace HarmonicDivergence

/-! ## The Main Theorem: Harmonic Series Diverges

The harmonic series ∑_{n=1}^∞ 1/n is not summable—equivalently, its partial sums
grow without bound. -/

/-- **Harmonic Series Divergence (Wiedijk #34)**

The harmonic series ∑_{n=1}^∞ 1/n diverges. More precisely, the sequence
n ↦ 1/n is not summable over the natural numbers.

This is formalized as: the function (fun n => 1 / (n : ℝ)) is not summable. -/
theorem harmonic_not_summable : ¬Summable (fun n : ℕ => 1 / (n : ℝ)) := by
  exact Real.not_summable_one_div_natCast

/-- Alternative formulation using n⁻¹ instead of 1/n -/
theorem harmonic_not_summable' : ¬Summable (fun n : ℕ => ((n : ℝ)⁻¹)) := by
  exact Real.not_summable_natCast_inv

/-! ## Partial Sums Tend to Infinity

An equivalent formulation: the partial sums of the harmonic series are unbounded
and in fact tend to infinity. -/

/-- The partial sums of 1/(n+1) tend to infinity.

Note: We use n+1 to avoid division by zero at n=0. The sum
∑_{k=0}^{n-1} 1/(k+1) = 1 + 1/2 + 1/3 + ... + 1/n → ∞ -/
theorem partial_sums_tendsto_atTop :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1))
      Filter.atTop Filter.atTop := by
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

/-! ## Why Does This Happen? Oresme's Grouping Argument

The classical proof groups terms to show each group sums to at least 1/2:

  1/1 ≥ 1/2
  1/2 ≥ 1/2
  1/3 + 1/4 > 1/4 + 1/4 = 1/2
  1/5 + 1/6 + 1/7 + 1/8 > 4 · (1/8) = 1/2
  1/9 + ... + 1/16 > 8 · (1/16) = 1/2
  ...

Since we can form infinitely many such groups, each contributing at least 1/2,
the series must diverge. -/

/-- Each term 1/n is positive for n > 0 -/
theorem one_div_nat_pos (n : ℕ) (hn : n ≠ 0) : (0 : ℝ) < 1 / n := by
  simp [Nat.pos_iff_ne_zero.mpr hn]

/-- The sum of terms from 2^k to 2^{k+1} - 1 is at least 1/2.
This is the key insight in Oresme's grouping argument. -/
theorem group_sum_ge_half (k : ℕ) (hk : k ≥ 1) :
    ∑ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / (i : ℕ) ≥ 1/2 := by
  -- The group from 2^k to 2^{k+1}-1 has 2^k terms
  -- Each term is ≥ 1/2^{k+1}
  -- So the sum is ≥ 2^k · (1/2^{k+1}) = 1/2
  have h1 : (2 : ℕ)^(k+1) - 1 ≥ 2^k := by
    have : 2^(k+1) = 2 * 2^k := by ring
    omega
  -- Each term 1/i is at least 1/2^{k+1} since i ≤ 2^{k+1} - 1 < 2^{k+1}
  have h2 : ∀ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / (i : ℕ) ≥ 1 / 2^(k+1) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi_pos : (0 : ℝ) < (i : ℕ) := by
      have h1 : 2^k ≥ 1 := Nat.one_le_two_pow
      have h2 : i ≥ 2^k := hi.1
      have h3 : i ≥ 1 := Nat.le_trans h1 h2
      exact Nat.cast_pos.mpr h3
    have h2k1_pos : (0 : ℝ) < 2^(k+1) := by positivity
    rw [ge_iff_le, div_le_div_iff h2k1_pos hi_pos]
    simp only [one_mul]
    have hle : i ≤ 2^(k+1) - 1 := hi.2
    have h2k1_ge : (2 : ℕ)^(k+1) ≥ 1 := Nat.one_le_two_pow
    have h_lt : i < 2^(k+1) := by omega
    exact_mod_cast le_of_lt h_lt
  have card_eq : (Finset.Icc (2^k) (2^(k+1) - 1)).card = 2^k := by
    rw [Nat.card_Icc]
    have h : 2^(k+1) - 1 + 1 - 2^k = 2^k := by
      have h1 : 2^(k+1) = 2 * 2^k := by ring
      have h2 : 2^(k+1) ≥ 1 := Nat.one_le_two_pow
      omega
    exact h
  have hsum : ∑ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / (i : ℕ) ≥
              ∑ _i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / 2^(k+1) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h2 i hi
  have hconst : ∑ _i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / 2^(k+1) =
                (Finset.Icc (2^k) (2^(k+1) - 1)).card * ((1 : ℝ) / 2^(k+1)) := by
    simp only [Finset.sum_const, smul_eq_mul]
    congr 1
    simp
  have hcard : (Finset.Icc (2^k) (2^(k+1) - 1)).card * ((1 : ℝ) / 2^(k+1)) = 1 / 2 := by
    rw [card_eq]
    have h2k_pos : (2 : ℝ)^k > 0 := by positivity
    have h2k1_pos : (2 : ℝ)^(k+1) > 0 := by positivity
    field_simp
    have : (2 : ℝ)^(k+1) = 2 * 2^k := by ring
    linarith
  linarith [hsum, hconst, hcard]

/-! ## Contrast with Convergent Series

While the harmonic series diverges, slight modifications can converge:
- ∑ 1/n² converges (Basel problem, = π²/6)
- ∑ 1/n^p converges for any p > 1

The harmonic series is right at the boundary of convergence. -/

/-- The p-series ∑ 1/n^p converges for p > 1.
This contrasts with the harmonic series (p = 1) which diverges. -/
theorem p_series_summable_of_gt_one (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / (n : ℝ)^p) := by
  have h : Summable (fun n : ℕ => ((n : ℝ)^p)⁻¹) := Real.summable_nat_rpow_inv.mpr hp
  convert h using 1
  ext n
  simp [div_eq_mul_inv]

/-! ## Asymptotic Growth Rate

The partial sums of the harmonic series grow like ln(n). More precisely,
H_n = ∑_{k=1}^n 1/k ≈ ln(n) + γ where γ ≈ 0.5772 is the Euler-Mascheroni constant.

This explains why the divergence is so slow: to reach a partial sum of 10,
you need about e^10 ≈ 22026 terms! -/

/-- The harmonic series grows unboundedly but very slowly.
For any bound M, there exists N such that H_n > M for n ≥ N. -/
theorem harmonic_eventually_exceeds (M : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, M < ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
  -- This follows from the partial sums tending to infinity
  have h := partial_sums_tendsto_atTop
  rw [Filter.tendsto_atTop_atTop] at h
  -- Ask for M + 1 to get a strict inequality
  obtain ⟨N, hN⟩ := h (M + 1)
  exact ⟨N, fun n hn => lt_of_lt_of_le (by linarith) (hN n hn)⟩

end HarmonicDivergence
