/-
  Erdős Problem #1149: Coprimality of n and ⌊n^α⌋

  Source: https://erdosproblems.com/1149
  Status: SOLVED (Bergelson-Richter 2017)

  Statement:
  Let α > 0 be a real number that is not an integer. Then the natural
  density of the set {n ≥ 1 : gcd(n, ⌊n^α⌋) = 1} is 6/π².

  Context:
  The value 6/π² = 1/ζ(2) is the probability that two "random" integers
  are coprime. This result shows that n and ⌊n^α⌋ behave as if they were
  "independent" from a coprimality standpoint, despite the deterministic
  relationship between them.

  Reference:
  - Bergelson, Richter (2017) [BeRi17]
  - [Va99, Problem 1.34]
-/

import Mathlib

open Finset Filter BigOperators Set

namespace Erdos1149

/-
## Definitions
-/

/-- The floor-power coprimality property: gcd(n, ⌊n^α⌋) = 1. -/
def IsFloorPowerCoprime (α : ℝ) (n : ℕ) : Prop :=
  Nat.Coprime n (Nat.floor ((n : ℝ) ^ α))

/-- The set of positive integers n where gcd(n, ⌊n^α⌋) = 1. -/
def coprimeFloorPowerSet (α : ℝ) : Set ℕ :=
  { n | 0 < n ∧ IsFloorPowerCoprime α n }

/-- Counting function for the coprime floor-power set in {1, ..., N}. -/
noncomputable def countCoprime (α : ℝ) (N : ℕ) : ℕ :=
  Set.ncard (coprimeFloorPowerSet α ∩ Set.Icc 1 N)

/-- Whether a set S ⊆ ℕ has natural density d: |S ∩ {1,...,N}| / N → d. -/
def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => (Set.ncard (S ∩ Set.Icc 1 N) : ℝ) / N)
    atTop (nhds d)

/-
## Properties of the Coprime Floor-Power Set
-/

/-- n = 1 is always coprime to any floor power, since gcd(1, m) = 1. -/
theorem one_isFloorPowerCoprime (α : ℝ) : IsFloorPowerCoprime α 1 :=
  Nat.coprime_one_left _

/-- 1 is always in the coprime floor-power set. -/
theorem one_mem_coprimeFloorPowerSet (α : ℝ) : 1 ∈ coprimeFloorPowerSet α :=
  ⟨Nat.one_pos, one_isFloorPowerCoprime α⟩

/-- The coprime floor-power set is always nonempty (contains 1). -/
theorem coprimeFloorPowerSet_nonempty (α : ℝ) : (coprimeFloorPowerSet α).Nonempty :=
  ⟨1, one_mem_coprimeFloorPowerSet α⟩

/-- If ⌊n^α⌋ = 1, then n is coprime to ⌊n^α⌋. This covers
    the regime 1 < n^α < 2 (e.g., small α or small n). -/
theorem coprime_of_floor_eq_one (α : ℝ) (n : ℕ)
    (h : Nat.floor ((n : ℝ) ^ α) = 1) : IsFloorPowerCoprime α n := by
  unfold IsFloorPowerCoprime
  rw [h]
  exact Nat.coprime_one_right n

/-
## The Main Theorem
-/

/-- **Bergelson-Richter Theorem (2017)**:
    For any non-integer α > 0, the natural density of
    {n ≥ 1 : gcd(n, ⌊n^α⌋) = 1} is 6/π².

    The value 6/π² = 1/ζ(2) is the "probability" that two random
    integers are coprime, suggesting n and ⌊n^α⌋ behave independently
    with respect to coprimality.

    Stated as: |{n ≤ N : gcd(n, ⌊n^α⌋) = 1}| / N → 6/π² as N → ∞. -/
axiom bergelson_richter (α : ℝ) (hα_pos : 0 < α)
    (hα_nonint : ∀ k : ℤ, (k : ℝ) ≠ α) :
    Filter.Tendsto
      (fun N : ℕ => (countCoprime α N : ℝ) / N)
      Filter.atTop
      (nhds (6 / Real.pi ^ 2))

/-- The density 6/π² ≈ 0.6079... is the reciprocal of ζ(2). -/
theorem density_equals_inv_zeta2 : 6 / Real.pi ^ 2 = 1 / (Real.pi ^ 2 / 6) := by
  ring

/-- **Erdős Problem #1149 is SOLVED**: the density exists and equals 6/π². -/
theorem erdos_1149_solved (α : ℝ) (hα_pos : 0 < α)
    (hα_nonint : ∀ k : ℤ, (k : ℝ) ≠ α) :
    Filter.Tendsto
      (fun N : ℕ => (countCoprime α N : ℝ) / N)
      Filter.atTop
      (nhds (6 / Real.pi ^ 2)) :=
  bergelson_richter α hα_pos hα_nonint

/-
## Properties and Context
-/

/-- The density 6/π² is positive (approximately 0.608). -/
theorem density_pos : 0 < 6 / Real.pi ^ 2 := by
  apply div_pos (by norm_num : (0:ℝ) < 6)
  exact sq_pos_of_pos Real.pi_pos

/-- The density 6/π² is less than 1 (since π > 3, so π² > 9 > 6). -/
theorem density_lt_one : 6 / Real.pi ^ 2 < 1 := by
  rw [div_lt_one (sq_pos_of_pos Real.pi_pos)]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  calc (6 : ℝ) < 3 ^ 2 := by norm_num
    _ < Real.pi ^ 2 := by nlinarith

/-- For integer α, the problem statement doesn't apply.
    When α is a positive integer, ⌊n^α⌋ = n^α exactly, and
    gcd(n, n^α) = n^gcd(1,α) = n for α ≥ 1.
    So the coprime set would be {1}, with density 0. -/
theorem integer_alpha_trivial (k : ℕ) (hk : 0 < k) :
    ∀ n : ℕ, 1 < n → ¬ Nat.Coprime n (n ^ k) := by
  intro n hn hcop
  have : n ∣ n ^ k := dvd_pow_self n (Nat.pos_iff_ne_zero.mp hk)
  have : n ∣ Nat.gcd n (n ^ k) := Nat.dvd_gcd dvd_rfl this
  rw [Nat.Coprime] at hcop
  rw [hcop] at this
  exact Nat.not_lt.mpr (Nat.le_of_dvd one_pos this) hn

/-- The density 6/π² lies strictly in the open interval (0, 1). -/
theorem density_mem_Ioo : 6 / Real.pi ^ 2 ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨density_pos, density_lt_one⟩

/-- The Bergelson-Richter theorem restated using HasNaturalDensity:
    the coprime floor-power set has natural density 6/π². -/
theorem bergelson_richter_density (α : ℝ) (hα_pos : 0 < α)
    (hα_nonint : ∀ k : ℤ, (k : ℝ) ≠ α) :
    HasNaturalDensity (coprimeFloorPowerSet α) (6 / Real.pi ^ 2) :=
  bergelson_richter α hα_pos hα_nonint

/-
## Connection to Coprime Probability

The value 6/π² = ∏_p (1 - 1/p²) where the product is over all primes p.
This is the "probability" that two uniformly random integers are coprime.

The Bergelson-Richter result shows that n and ⌊n^α⌋, despite being
deterministically related, satisfy the same coprimality statistics as
independent random integers.
-/

/-- The "probability" that two random integers are coprime is 6/π².
    More precisely, lim_{N→∞} |{(a,b) ∈ [1,N]² : gcd(a,b) = 1}| / N² = 6/π².
    This is a classical result (Euler product for 1/ζ(2)). -/
axiom random_coprime_density :
    Filter.Tendsto
      (fun N : ℕ => (Set.ncard {p : ℕ × ℕ | p.1 ∈ Set.Icc 1 N ∧ p.2 ∈ Set.Icc 1 N ∧
        Nat.Coprime p.1 p.2} : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop
      (nhds (6 / Real.pi ^ 2))

/-- Coprime pair counting via Finset (decidable/computable).
    Counts |{(a,b) ∈ [1,N]² : gcd(a,b) = 1}| using a finite computation. -/
def countCoprimePairs (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun p => Nat.Coprime p.1 p.2)).card

/-- Coprime pair symmetry: (a,b) coprime iff (b,a) coprime.
    Hence countCoprimePairs counts each pair's contribution equally. -/
theorem coprime_pair_symm (a b : ℕ) : Nat.Coprime a b ↔ Nat.Coprime b a :=
  ⟨Nat.Coprime.symm, Nat.Coprime.symm⟩

/-- The coprime pair count at N = 1 is exactly 1: only (1,1). -/
theorem countCoprimePairs_one : countCoprimePairs 1 = 1 := by
  native_decide

/-
## Computational Verification (small cases)

For α = 1/2 (square root), we verify coprimality for small n:
- n = 1: ⌊1^{0.5}⌋ = 1, gcd(1,1) = 1 ✓
- n = 2: ⌊2^{0.5}⌋ = 1, gcd(2,1) = 1 ✓
- n = 3: ⌊3^{0.5}⌋ = 1, gcd(3,1) = 1 ✓
- n = 4: ⌊4^{0.5}⌋ = 2, gcd(4,2) = 2 ✗
- n = 5: ⌊5^{0.5}⌋ = 2, gcd(5,2) = 1 ✓
- n = 6: ⌊6^{0.5}⌋ = 2, gcd(6,2) = 2 ✗
- n = 7: ⌊7^{0.5}⌋ = 2, gcd(7,2) = 1 ✓
- n = 8: ⌊8^{0.5}⌋ = 2, gcd(8,2) = 2 ✗
- n = 9: ⌊9^{0.5}⌋ = 3, gcd(9,3) = 3 ✗
- n = 10: ⌊10^{0.5}⌋ = 3, gcd(10,3) = 1 ✓

Count in {1,...,10}: 6 out of 10 = 0.6 (close to 6/π² ≈ 0.608)
-/

/-
## Summary

**Erdős Problem #1149** asks for the density of integers n where
gcd(n, ⌊n^α⌋) = 1, for non-integer α > 0.

**Answer**: 6/π² ≈ 0.608 (Bergelson-Richter 2017)

**Key insight**: n and ⌊n^α⌋ are coprime with the same "probability"
as two random integers, despite the deterministic relationship.

**Proof method**: Uses ergodic theory and the theory of multiplicative
functions along polynomial sequences (Bergelson-Richter 2017).

**Related**: 6/π² = 1/ζ(2) = ∏_p (1 - 1/p²) (Euler product formula).
-/

/-
## Möbius Inversion Infrastructure

Path to proving random_coprime_density:
Step 1: ∑_{d|n} μ(d) = [n=1] (Möbius inversion principle)
Step 2: countCoprimePairs N = ∑_{d=1}^N μ(d)⌊N/d⌋² (counting identity)
Step 3: countCoprimePairs N / N² → 6/π² (asymptotic analysis)
-/

/-- Key identity: ∑_{d | gcd(a,b)} μ(d) = 1 if gcd(a,b) = 1, else 0.
    This is the Möbius inversion principle applied to coprimality detection.
    Follows from (ζ * μ) = 1 in the Dirichlet convolution ring. -/
theorem moebius_sum_divisors_eq (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) =
      if n = 1 then 1 else 0 := by
  -- From (ζ * μ) = 1 (Dirichlet convolution identity)
  -- (ζ * μ)(n) = ∑_{d|n} ζ(d) · μ(n/d) = ∑_{d|n} μ(n/d) = 1(n)
  -- By change of variable over divisors, ∑_{d|n} μ(d) = 1(n) as well
  sorry

/-- The number of multiples of d in {1, ..., N} is ⌊N/d⌋. -/
theorem card_multiples (d N : ℕ) (hd : 0 < d) :
    (Finset.filter (fun a => d ∣ a) (Finset.Icc 1 N)).card = N / d := by
  sorry -- Routine Finset counting, good Aristotle candidate

/-- For prime p, exactly ⌊N/p⌋² pairs (a,b) in [1,N]² have p | gcd(a,b). -/
theorem pairs_with_common_factor (p N : ℕ) (hp : Nat.Prime p) :
    ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun ab => p ∣ Nat.gcd ab.1 ab.2)).card = (N / p) ^ 2 := by
  sorry -- Counts pairs where p | a and p | b

/-- The "probability" interpretation: 6/π² = 1/ζ(2).
    Since ζ(2) = π²/6 (Basel problem), we have 6/π² = 1/ζ(2). -/
theorem six_div_pi_sq_eq_inv_zeta_two :
    6 / Real.pi ^ 2 = (Real.pi ^ 2 / 6)⁻¹ := by
  rw [inv_div]

end Erdos1149
