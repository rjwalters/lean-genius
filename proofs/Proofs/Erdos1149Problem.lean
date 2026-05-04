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
import Proofs.BaselProblemOQ04OQ03

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
    Proved via Möbius inversion + Tannery's theorem (BaselProblemOQ04OQ03). -/
theorem random_coprime_density :
    Filter.Tendsto
      (fun N : ℕ => (Set.ncard {p : ℕ × ℕ | p.1 ∈ Set.Icc 1 N ∧ p.2 ∈ Set.Icc 1 N ∧
        Nat.Coprime p.1 p.2} : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop
      (nhds (6 / Real.pi ^ 2)) := by
  suffices h_eq : ∀ N : ℕ, Set.ncard {p : ℕ × ℕ | p.1 ∈ Set.Icc 1 N ∧
      p.2 ∈ Set.Icc 1 N ∧ Nat.Coprime p.1 p.2} =
    BaselProblemOQ04OQ03.countCoprimePairs N by
    simp_rw [h_eq]; exact BaselProblemOQ04OQ03.coprime_pair_density_limit
  intro N
  have h_set : {p : ℕ × ℕ | p.1 ∈ Set.Icc 1 N ∧ p.2 ∈ Set.Icc 1 N ∧
      Nat.Coprime p.1 p.2} =
      ↑((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.Coprime p.1 p.2)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
               Finset.mem_Icc, Set.mem_Icc]
    tauto
  rw [h_set, Set.ncard_coe_Finset]
  simp [BaselProblemOQ04OQ03.countCoprimePairs]

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
  -- Proof via μ * ζ = ε (Dirichlet identity in ArithmeticFunction ℤ)
  trans (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
         ↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ)) n)
  · rw [ArithmeticFunction.mul_apply]
    simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
    have h_simp : ∀ x ∈ n.divisorsAntidiagonal,
        ArithmeticFunction.moebius x.1 * (↑(if x.2 = 0 then (0 : ℕ) else 1) : ℤ) =
        ArithmeticFunction.moebius x.1 := by
      intro x hx
      have hmem := Nat.mem_divisorsAntidiagonal.mp hx
      have hx2 : x.2 ≠ 0 := by
        intro h; exact hmem.2 (by rw [← hmem.1, h, mul_zero])
      simp [hx2]
    rw [Finset.sum_congr rfl h_simp]
    symm
    apply Finset.sum_nbij Prod.fst
    · intro x hx
      have hmem := Nat.mem_divisorsAntidiagonal.mp hx
      exact Nat.mem_divisors.mpr ⟨⟨x.2, hmem.1.symm⟩, hmem.2⟩
    · intro x₁ hx₁ x₂ hx₂ h
      have h1 := (Nat.mem_divisorsAntidiagonal.mp hx₁).1
      have h2 := (Nat.mem_divisorsAntidiagonal.mp hx₂).1
      have h2_ne := (Nat.mem_divisorsAntidiagonal.mp hx₂).2
      have h_ne : x₂.1 ≠ 0 := by
        intro hz; exact h2_ne (by rw [← h2, hz, zero_mul])
      have h_eq : x₁.1 * x₁.2 = x₂.1 * x₂.2 := h1.trans h2.symm
      ext
      · exact h
      · exact mul_left_cancel₀ h_ne (by rwa [h] at h_eq)
    · intro d hd
      exact ⟨(d, n / d), Nat.mem_divisorsAntidiagonal.mpr
        ⟨Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), hn.ne'⟩, rfl⟩
    · intro _ _; rfl
  · rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- The number of multiples of d in {1, ..., N} is ⌊N/d⌋. -/
theorem card_multiples (d N : ℕ) (hd : 0 < d) :
    (Finset.filter (fun a => d ∣ a) (Finset.Icc 1 N)).card = N / d := by
  -- Bijection: multiples of d in [1,N] ↔ {0,...,N/d-1} via a ↦ a/d - 1
  have h_eq : Finset.filter (fun a => d ∣ a) (Finset.Icc 1 N) =
      (Finset.range (N / d)).image (fun j => (j + 1) * d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨ha1, haN⟩, ⟨k, rfl⟩⟩
      have hk_pos : 0 < k := by
        by_contra h; push_neg at h; interval_cases k; simp at ha1
      have hk_le : k ≤ N / d := by
        rw [Nat.le_div_iff_mul_le hd]
        calc k * d = d * k := mul_comm k d
          _ ≤ N := haN
      exact ⟨k - 1, by omega, by rw [Nat.sub_add_cancel (by omega : 1 ≤ k), mul_comm]⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_left d (j + 1)⟩
      · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hd.ne')
      · calc (j + 1) * d ≤ N / d * d := by nlinarith
          _ ≤ N := Nat.div_mul_le_self N d
  rw [h_eq]
  rw [Finset.card_image_of_injective _ (fun a b h => by
    have := mul_right_cancel₀ hd.ne' h; omega)]
  exact Finset.card_range _

/-- For prime p, exactly ⌊N/p⌋² pairs (a,b) in [1,N]² have p | gcd(a,b). -/
theorem pairs_with_common_factor (p N : ℕ) (hp : Nat.Prime p) :
    ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun ab => p ∣ Nat.gcd ab.1 ab.2)).card = (N / p) ^ 2 := by
  -- p | gcd(a,b) ↔ p | a ∧ p | b: factor the product set
  have h_filter : (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun ab => p ∣ Nat.gcd ab.1 ab.2) =
      Finset.filter (fun a => p ∣ a) (Finset.Icc 1 N) ×ˢ
      Finset.filter (fun b => p ∣ b) (Finset.Icc 1 N) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨ha, hb⟩, hdvd⟩
      exact ⟨⟨ha, dvd_trans hdvd (Nat.gcd_dvd_left a b)⟩,
             ⟨hb, dvd_trans hdvd (Nat.gcd_dvd_right a b)⟩⟩
    · rintro ⟨⟨ha, hdva⟩, ⟨hb, hdvb⟩⟩
      exact ⟨⟨ha, hb⟩, Nat.dvd_gcd hdva hdvb⟩
  rw [h_filter, Finset.card_product, card_multiples p N hp.pos, sq]

/-- The "probability" interpretation: 6/π² = 1/ζ(2).
    Since ζ(2) = π²/6 (Basel problem), we have 6/π² = 1/ζ(2). -/
theorem six_div_pi_sq_eq_inv_zeta_two :
    6 / Real.pi ^ 2 = (Real.pi ^ 2 / 6)⁻¹ := by
  rw [inv_div]

end Erdos1149
