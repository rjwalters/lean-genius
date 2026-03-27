/-
Erdős Problem #410: Iterated Sum of Divisors Growth

**Problem Statement (OPEN)**

Let σ₁(n) = σ(n), the sum of divisors function, and σₖ(n) = σ(σₖ₋₁(n)).

Is it true that lim_{k → ∞} σₖ(n)^{1/k} = ∞ for all n ≥ 2?

**Background:**
- σ(n) = sum of all divisors of n (including 1 and n)
- σₖ is the k-th iterate of σ
- We ask about the exponential growth rate of iterates

**Known Results:**
- σ(n) > n for all n > 1 (abundancy)
- The iterates grow strictly and tend to ∞
- σ is multiplicative with explicit formula for prime powers
- Related to perfect numbers and aliquot sequences

**Status:** OPEN

**Reference:** [ErGr80], Guy Problem B9, OEIS A007497

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Nat ArithmeticFunction Filter

namespace Erdos410

-- ## Part 1: The Sum of Divisors Function

-- σ(n) = sum of all positive divisors of n.
-- sigma 1 : ℕ → ℕ gives σ(n) from Mathlib.

-- σ(1) = 1
theorem sigma_one : sigma 1 1 = 1 := by native_decide

-- σ(2) = 3
theorem sigma_two : sigma 1 2 = 3 := by native_decide

-- σ(3) = 4
theorem sigma_three : sigma 1 3 = 4 := by native_decide

-- σ(4) = 7
theorem sigma_four : sigma 1 4 = 7 := by native_decide

-- σ(6) = 12
theorem sigma_six : sigma 1 6 = 12 := by native_decide

-- σ(7) = 8
theorem sigma_seven : sigma 1 7 = 8 := by native_decide

-- σ(12) = 28
theorem sigma_twelve : sigma 1 12 = 28 := by native_decide

-- σ(28) = 56
theorem sigma_twentyeight : sigma 1 28 = 56 := by native_decide

/-- σ(n) > 0 for n > 0 -/
theorem sigma_pos (n : ℕ) (hn : n > 0) : sigma 1 n > 0 := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
  calc sigma 1 n = ∑ d ∈ n.divisors, d ^ 1 := by simp [sigma_apply]
    _ ≥ n ^ 1 := Finset.single_le_sum (fun d _ => Nat.zero_le _) hmem
    _ = n := by ring
    _ > 0 := hn

/-- σ(n) ≥ n for n ≥ 1 -/
theorem sigma_ge_self (n : ℕ) (hn : 0 < n) : sigma 1 n ≥ n := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
  calc sigma 1 n = ∑ d ∈ n.divisors, d ^ 1 := by simp [sigma_apply]
    _ ≥ n ^ 1 := Finset.single_le_sum (fun d _ => Nat.zero_le _) hmem
    _ = n := by ring

/-- σ(n) > n for n > 1 (n has at least divisors 1 and n) -/
theorem sigma_gt_n (n : ℕ) (hn : n > 1) : sigma 1 n > n := by
  have h1mem : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, (by omega : n ≠ 0)⟩
  have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, (by omega : n ≠ 0)⟩
  have hne : (1 : ℕ) ≠ n := by omega
  have hsub : {1, n} ⊆ n.divisors := by
    intro d hd; simp at hd; rcases hd with rfl | rfl <;> assumption
  calc sigma 1 n = ∑ d ∈ n.divisors, d ^ 1 := by simp [sigma_apply]
    _ ≥ ∑ d ∈ ({1, n} : Finset ℕ), d ^ 1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => Nat.zero_le _)
    _ = 1 ^ 1 + n ^ 1 := by rw [Finset.sum_pair hne]
    _ = 1 + n := by ring
    _ > n := by omega

/-- σ(n) ≥ n + 1 for n > 1 -/
theorem sigma_lower_bound (n : ℕ) (hn : n > 1) : sigma 1 n ≥ n + 1 := by
  have := sigma_gt_n n hn
  omega

/-- σ(p) = p + 1 for prime p -/
theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma 1 p = p + 1 := by
  simp [sigma_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne']
  ring

/-- σ is multiplicative -/
theorem sigma_multiplicative : ArithmeticFunction.IsMultiplicative (sigma 1) :=
  sigma_isMultiplicative

-- ## Part 2: Iterated Sum of Divisors

/-- The k-th iterate of σ -/
noncomputable def sigmaIterate (k n : ℕ) : ℕ :=
  (sigma 1)^[k] n

-- Base case: σ₀(n) = n
theorem sigma_iterate_zero (n : ℕ) : sigmaIterate 0 n = n := by
  simp only [sigmaIterate, Function.iterate_zero_apply]

-- Recursion: σₖ₊₁(n) = σ(σₖ(n))
theorem sigma_iterate_succ (k n : ℕ) :
    sigmaIterate (k + 1) n = sigma 1 (sigmaIterate k n) := by
  simp only [sigmaIterate, Function.iterate_succ_apply']

-- σ₁(n) = σ(n)
theorem sigma_iterate_one (n : ℕ) : sigmaIterate 1 n = sigma 1 n := by
  simp only [sigmaIterate, Function.iterate_one]

-- ## Part 3: Explicit Computations of Iterates

-- For n = 2: σ₁(2) = 3, σ₂(2) = σ(3) = 4, σ₃(2) = σ(4) = 7, σ₄(2) = σ(7) = 8
theorem sigma_chain_2 :
    sigma 1 2 = 3 ∧ sigma 1 3 = 4 ∧ sigma 1 4 = 7 ∧ sigma 1 7 = 8 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- For n = 6 (perfect): σ(6) = 12, σ(12) = 28, σ(28) = 56
theorem sigma_chain_6 :
    sigma 1 6 = 12 ∧ sigma 1 12 = 28 ∧ sigma 1 28 = 56 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- Iterated chain for n=2 using sigmaIterate
theorem sigma_iterate_2_1 : sigmaIterate 1 2 = 3 := by
  rw [sigma_iterate_one]; native_decide

theorem sigma_iterate_2_2 : sigmaIterate 2 2 = 4 := by
  rw [sigma_iterate_succ, sigma_iterate_one]; native_decide

theorem sigma_iterate_2_3 : sigmaIterate 3 2 = 7 := by
  rw [sigma_iterate_succ, sigma_iterate_succ, sigma_iterate_one]; native_decide

theorem sigma_iterate_2_4 : sigmaIterate 4 2 = 8 := by
  rw [sigma_iterate_succ, sigma_iterate_succ, sigma_iterate_succ, sigma_iterate_one]; native_decide

-- ## Part 4: Growth of Iterates

/-- σₖ(n) ≥ n for n > 0 (by induction on k) -/
theorem sigma_iterate_ge (n : ℕ) (hn : n > 0) (k : ℕ) :
    sigmaIterate k n ≥ n := by
  induction k with
  | zero => simp [sigmaIterate]
  | succ k ih =>
    rw [sigma_iterate_succ]
    calc sigma 1 (sigmaIterate k n)
      ≥ sigmaIterate k n := sigma_ge_self _ (by omega)
      _ ≥ n := ih

/-- σₖ(n) > 1 for n > 1 -/
theorem sigma_iterate_gt_one (n : ℕ) (hn : n > 1) (k : ℕ) :
    sigmaIterate k n > 1 := by
  have h := sigma_iterate_ge n (by omega : n > 0) k
  omega

/-- σₖ(n) is strictly increasing in k for n > 1 -/
theorem sigma_iterate_increasing (n : ℕ) (hn : n > 1) (k : ℕ) :
    sigmaIterate k n < sigmaIterate (k + 1) n := by
  rw [sigma_iterate_succ]
  exact sigma_gt_n _ (sigma_iterate_gt_one n hn k)

/-- σₖ(n) ≥ n + k for n > 1 (iterates grow at least linearly) -/
theorem sigma_iterate_linear_lower (n : ℕ) (hn : n > 1) (k : ℕ) :
    sigmaIterate k n ≥ n + k := by
  induction k with
  | zero => simp [sigmaIterate]
  | succ k ih =>
    rw [sigma_iterate_succ]
    have hgt1 : sigmaIterate k n > 1 := sigma_iterate_gt_one n hn k
    have hgt : sigma 1 (sigmaIterate k n) > sigmaIterate k n := sigma_gt_n _ hgt1
    omega

/-- σₖ(n) → ∞ as k → ∞ for n > 1 -/
theorem sigma_iterate_tendsto_infty (n : ℕ) (hn : n > 1) :
    Tendsto (fun k => sigmaIterate k n) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  use b
  intro k hk
  calc (sigmaIterate k n : ℕ) ≥ n + k := sigma_iterate_linear_lower n hn k
    _ ≥ 2 + k := by omega
    _ ≥ k := by omega
    _ ≥ b := hk

-- ## Part 5: Special Numbers

/-- A number is perfect if σ(n) = 2n -/
def IsPerfect (n : ℕ) : Prop := sigma 1 n = 2 * n

/-- A number is abundant if σ(n) > 2n -/
def IsAbundant (n : ℕ) : Prop := sigma 1 n > 2 * n

/-- A number is deficient if σ(n) < 2n -/
def IsDeficient (n : ℕ) : Prop := sigma 1 n < 2 * n

/-- 6 is a perfect number -/
theorem perfect_6 : IsPerfect 6 := by
  unfold IsPerfect; native_decide

/-- 28 is a perfect number -/
theorem perfect_28 : IsPerfect 28 := by
  unfold IsPerfect; native_decide

/-- 496 is a perfect number -/
theorem perfect_496 : IsPerfect 496 := by
  unfold IsPerfect; native_decide

/-- 12 is an abundant number -/
theorem abundant_12 : IsAbundant 12 := by
  unfold IsAbundant; native_decide

/-- 2 is a deficient number -/
theorem deficient_2 : IsDeficient 2 := by
  unfold IsDeficient; native_decide

-- ## Part 6: Aliquot Sequences

/-- Aliquot function: s(n) = σ(n) - n (sum of proper divisors) -/
def aliquot (n : ℕ) : ℕ := sigma 1 n - n

/-- s(6) = 6 (perfect: proper divisors 1+2+3=6) -/
theorem aliquot_six : aliquot 6 = 6 := by
  unfold aliquot; native_decide

/-- s(28) = 28 (perfect: proper divisors 1+2+4+7+14=28) -/
theorem aliquot_twentyeight : aliquot 28 = 28 := by
  unfold aliquot; native_decide

/-- s(12) = 16 (abundant: proper divisors 1+2+3+4+6=16) -/
theorem aliquot_twelve : aliquot 12 = 16 := by
  unfold aliquot; native_decide

-- ## Part 7: The Main Conjecture

/-- The normalized growth rate σₖ(n)^{1/k} -/
noncomputable def growthRate (n k : ℕ) : ℝ :=
  (sigmaIterate k n : ℝ) ^ (1 / (k : ℝ))

/-- Erdős Conjecture #410: σₖ(n)^{1/k} → ∞ -/
def ErdosConjecture410 : Prop :=
  ∀ n > 1, Tendsto (fun k => growthRate n k) atTop atTop

/-- Main formal statement (equivalent reformulation) -/
theorem erdos_410_statement : ErdosConjecture410 ↔
    ∀ n > 1, Tendsto (fun k : ℕ => ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  unfold ErdosConjecture410 growthRate sigmaIterate
  rfl

/-- Helper: (x^{1/k})^k = x for x ≥ 0 and k ≥ 1.
    Uses the exponent identity (1/k) · k = 1. -/
private theorem rpow_inv_pow_eq {x : ℝ} {k : ℕ} (hx : 0 ≤ x) (hk : k ≠ 0) :
    (x ^ (1 / (k : ℝ))) ^ k = x := by
  rw [← Real.rpow_natCast (x ^ (1 / (k : ℝ))) k, ← Real.rpow_mul hx,
      one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk), Real.rpow_one]

/-- Equivalent: σₖ(n) grows faster than any exponential c^k.
    Proved from the characterization of limits: x_k^{1/k} → ∞ iff
    x_k eventually exceeds any geometric sequence c^k. -/
theorem conjecture_equiv_exp : ErdosConjecture410 ↔
    ∀ n > 1, ∀ c > (0 : ℝ), ∃ K : ℕ, ∀ k ≥ K, (sigmaIterate k n : ℝ) > c ^ k := by
  unfold ErdosConjecture410
  constructor
  · -- Forward: Tendsto (growth rate → ∞) implies eventual domination of any c^k
    intro h n hn c hc
    obtain ⟨K₀, hK₀⟩ := (tendsto_atTop_atTop.mp (h n hn)) (c + 1)
    refine ⟨max K₀ 1, fun k hk => ?_⟩
    have hk₀ : K₀ ≤ k := (le_max_left _ _).trans hk
    have hk_ne : (k : ℕ) ≠ 0 := by omega
    have hge := hK₀ k hk₀
    unfold growthRate at hge
    have hx_nn : (0 : ℝ) ≤ (sigmaIterate k n : ℝ) := Nat.cast_nonneg _
    have hpow_le : (c + 1) ^ k ≤ (sigmaIterate k n : ℝ) := by
      have := pow_le_pow_left (by linarith : (0 : ℝ) ≤ c + 1) hge k
      rwa [rpow_inv_pow_eq hx_nn hk_ne] at this
    linarith [pow_lt_pow_left (show c < c + 1 by linarith) (le_of_lt hc) hk_ne]
  · -- Backward: eventual domination of any c^k implies growth rate → ∞
    intro h n hn
    rw [tendsto_atTop_atTop]
    intro b
    by_cases hb : b ≤ 0
    · refine ⟨1, fun k _ => ?_⟩
      unfold growthRate
      exact le_trans hb (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · push_neg at hb
      obtain ⟨K₀, hK₀⟩ := h n hn b hb
      refine ⟨max K₀ 1, fun k hk => ?_⟩
      have hk₀ : K₀ ≤ k := (le_max_left _ _).trans hk
      have hk_ne : (k : ℕ) ≠ 0 := by omega
      have hgt := hK₀ k hk₀
      have hx_nn : (0 : ℝ) ≤ (sigmaIterate k n : ℝ) := Nat.cast_nonneg _
      unfold growthRate
      by_contra hlt
      push_neg at hlt
      have hle : (sigmaIterate k n : ℝ) ≤ b ^ k := by
        have := pow_le_pow_left (Real.rpow_nonneg hx_nn _) (le_of_lt hlt) k
        rwa [rpow_inv_pow_eq hx_nn hk_ne] at this
      linarith

-- ## Part 8: Bounds on σ

/-- Robin's inequality: σ(n) < e^γ · n · ln(ln(n)) for n ≥ 5041
    (This is equivalent to the Riemann Hypothesis - Robin 1984) -/
axiom robin_inequality :
  ∀ n : ℕ, n ≥ 5041 → (sigma 1 n : ℝ) < Real.exp 0.5772 * n * Real.log (Real.log n)

/-- Average σ(n)/n tends to π²/6.
    (Deep result from analytic number theory via Euler products; beyond current Mathlib.) -/
axiom average_sigma : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
    |(∑ k ∈ Finset.range n, (sigma 1 k : ℝ) / k) / n - Real.pi ^ 2 / 6| < ε

-- ## Part 9: Structural Properties of Iterates

/-- The iterate sequence is strictly monotone for n > 1 -/
theorem sigma_iterate_strict_mono (n : ℕ) (hn : n > 1) :
    StrictMono (fun k => sigmaIterate k n) :=
  strictMono_nat_of_lt_succ (fun k => sigma_iterate_increasing n hn k)

/-- σ(σ(n)) > σ(n) for n > 1 -/
theorem sigma_sigma_gt (n : ℕ) (hn : n > 1) :
    sigma 1 (sigma 1 n) > sigma 1 n := by
  have h := sigma_gt_n n hn
  exact sigma_gt_n (sigma 1 n) (by omega)

/-- For perfect n: σ(n) = 2n, so σ₂(n) = σ(2n) -/
theorem sigma_iterate_perfect (n : ℕ) (hp : IsPerfect n) :
    sigmaIterate 2 n = sigma 1 (2 * n) := by
  rw [sigma_iterate_succ, sigma_iterate_one, hp]

-- ## Part 10: Summary

/-
**Erdős Problem #410: OPEN**

**Conjecture:** lim_{k → ∞} σₖ(n)^{1/k} = ∞ for all n ≥ 2.

**What we proved:**
- σ(n) > n for n > 1 (from first principles)
- σ(p) = p + 1 for primes
- σₖ(n) is strictly increasing in k for n > 1
- σₖ(n) grows at least linearly: σₖ(n) ≥ n + k
- σₖ(n) → ∞ as k → ∞
- The iterate sequence is strictly monotone
- Verified σ chains for n = 2, 3, 6
- 6, 28, 496 are perfect numbers
- The conjecture is equivalent to super-exponential growth (proved from limit theory)

**Remaining axioms (2):**
- robin_inequality: Equivalent to the Riemann Hypothesis (Robin 1984), unprovable
- average_sigma: Deep analytic number theory (Euler products), not in Mathlib

**What remains open:**
- Whether the growth is super-exponential (the actual conjecture)
- The answer for any specific n ≥ 2

**Related:** Aliquot sequences, perfect numbers, Guy Problem B9
-/

end Erdos410
