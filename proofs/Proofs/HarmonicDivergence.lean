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

/-- The sum of two consecutive terms from 2^k to 2^{k+1} - 1 is at least 1/2.
This is the key insight in Oresme's grouping argument. -/
theorem group_sum_ge_half (k : ℕ) (hk : k ≥ 1) :
    ∑ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / i ≥ 1/2 := by
  -- The group from 2^k to 2^{k+1}-1 has 2^k terms
  -- Each term is ≥ 1/2^{k+1}
  -- So the sum is ≥ 2^k · (1/2^{k+1}) = 1/2
  have h1 : (2 : ℕ)^(k+1) - 1 ≥ 2^k := by
    have : 2^(k+1) = 2 * 2^k := by ring
    omega
  have h2 : ∀ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / i ≥ 1 / 2^(k+1) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi_pos : (0 : ℝ) < i := by
      have : 2^k ≥ 1 := Nat.one_le_two_pow
      linarith [hi.1]
    have h2k1_pos : (0 : ℝ) < 2^(k+1) := by positivity
    rw [div_le_div_iff (by positivity : (0 : ℝ) < 1) hi_pos]
    rw [div_le_div_iff (by positivity : (0 : ℝ) < 1) h2k1_pos]
    simp only [one_mul]
    have : i ≤ 2^(k+1) - 1 := hi.2
    have : (i : ℝ) ≤ 2^(k+1) - 1 := by exact Nat.cast_le.mpr this
    have h2k1_nat : (2 : ℝ)^(k+1) = ((2^(k+1) : ℕ) : ℝ) := by simp
    linarith
  have card_eq : (Finset.Icc (2^k) (2^(k+1) - 1)).card = 2^k := by
    rw [Finset.card_Icc]
    have h : 2^(k+1) - 1 - 2^k + 1 = 2^k := by
      have : 2^(k+1) = 2 * 2^k := by ring
      omega
    exact h
  calc ∑ i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / i
      ≥ ∑ _i ∈ Finset.Icc (2^k) (2^(k+1) - 1), (1 : ℝ) / 2^(k+1) := by
          apply Finset.sum_le_sum
          intro i hi
          exact h2 i hi
    _ = (Finset.Icc (2^k) (2^(k+1) - 1)).card • ((1 : ℝ) / 2^(k+1)) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = 2^k * (1 / 2^(k+1)) := by rw [card_eq]; ring
    _ = 1 / 2 := by
          have : (2 : ℝ)^(k+1) = 2 * 2^k := by ring
          field_simp
          ring

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
  obtain ⟨N, hN⟩ := h M
  exact ⟨N, fun n hn => hN n hn⟩

end HarmonicDivergence
