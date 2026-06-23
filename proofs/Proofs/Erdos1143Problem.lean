/-
  Erdős Problem #1143: Covering Intervals with Multiples of Primes

  Source: https://erdosproblems.com/1143
  Status: OPEN

  Statement:
  Let p₁ < p₂ < ··· < pᵤ be primes and k ≥ 1. Define F_k(p₁,...,pᵤ) as the
  minimum number of integers in any interval of k consecutive integers that
  are divisible by at least one of the pᵢ. Estimate F_k(p₁,...,pᵤ),
  particularly when k = αpᵤ for constant α > 2.

  Context:
  By inclusion-exclusion, the expected proportion of integers divisible by
  at least one of p₁,...,pᵤ is 1 - ∏(1 - 1/pᵢ). For k = αpᵤ, the interval
  is long enough that multiple complete periods of each prime fit inside,
  so F_k should be close to k · (1 - ∏(1 - 1/pᵢ)).

  Known results:
  - Erdős and Selfridge found the exact bound for 2 < α < 3 (paper not located)
  - For α > 3, very little is known
  - Related to Problem #970 (Jacobsthal's function)

  References:
  - [Va99, Problem 1.8]
-/

import Mathlib

open Finset BigOperators

namespace Erdos1143

/-
## Definitions
-/

/-- The set of integers in [a, a+k) divisible by at least one prime in a list. -/
def coveredInInterval (primes : Finset ℕ) (a k : ℕ) : Finset ℕ :=
  (Finset.Ico a (a + k)).filter (fun n => ∃ p ∈ primes, p ∣ n)

/-- F_k(p₁,...,pᵤ): the minimum number of integers in any interval of k
    consecutive integers that are divisible by at least one of the primes. -/
noncomputable def coveringFunction (primes : Finset ℕ) (k : ℕ) : ℕ :=
  ⨅ (a : ℕ), (coveredInInterval primes a k).card

/-- The expected density of integers divisible by at least one prime.
    By inclusion-exclusion, this is 1 - ∏ᵢ(1 - 1/pᵢ). -/
noncomputable def expectedDensity (primes : Finset ℕ) : ℝ :=
  1 - ∏ p ∈ primes, (1 - 1 / (p : ℝ))

/-
## Basic Properties
-/

/-- The covering count is at most k (trivially, since we're in an interval of length k). -/
theorem covering_le_k (primes : Finset ℕ) (k : ℕ) :
    coveringFunction primes k ≤ k := by
  unfold coveringFunction
  apply ciInf_le_of_le ⟨0, fun _ ⟨_, h⟩ => h ▸ Nat.zero_le _⟩ 0
  unfold coveredInInterval
  calc ((Finset.Ico 0 (0 + k)).filter _).card
      ≤ (Finset.Ico 0 (0 + k)).card := Finset.card_filter_le _ _
    _ = k := by simp

/-- For a single prime p, F_k({p}) = ⌊k/p⌋ or ⌈k/p⌉.
    More precisely, in any k consecutive integers, at least ⌊k/p⌋ are
    divisible by p, and at most ⌈k/p⌉. -/
theorem single_prime_lower (p k : ℕ) (hp : Nat.Prime p) (hk : k ≥ 1) :
    coveringFunction {p} k ≥ k / p := by
  unfold coveringFunction coveredInInterval
  simp only [Finset.mem_singleton, exists_eq_left]
  rw [ge_iff_le]
  -- Goal: k / p ≤ ⨅ a, (Ico a (a + k) |>.filter (p ∣ ·)).card
  -- For all a, inject range(k/p) into multiples of p in [a, a+k)
  -- via i ↦ (⌈a/p⌉ + i) * p where ⌈a/p⌉ = (a + (p-1)) / p
  apply le_ciInf
  intro a
  have hp_pos : 0 < p := hp.pos
  -- g maps i to the (⌈a/p⌉ + i)-th multiple of p
  set g := fun i => ((a + (p - 1)) / p + i) * p
  -- g is injective (cancel p > 0)
  have hg_inj : Function.Injective g := by
    intro i j hij; simp only [g] at hij
    have := mul_right_cancel₀ hp_pos.ne' hij; omega
  -- Image of range(k/p) under g lies in filter set
  have hsub : (Finset.range (k / p)).image g ⊆
      (Finset.Ico a (a + k)).filter (p ∣ ·) := by
    intro n hn
    simp only [Finset.mem_image, g] at hn
    obtain ⟨i, hi, rfl⟩ := hn
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, dvd_mul_of_dvd_right (dvd_refl p) _⟩
    · -- Lower bound: a ≤ ((a+(p-1))/p + i) * p
      -- ⌈a/p⌉*p ≥ a by ceiling property, adding i only increases
      have hceil_lb : a ≤ (a + (p - 1)) / p * p := by
        have h1 := Nat.div_add_mod (a + (p - 1)) p
        rw [mul_comm] at h1  -- p * (../p) → (../p) * p to match goal
        have h2 := Nat.mod_lt (a + (p - 1)) hp_pos
        omega
      calc a ≤ (a + (p - 1)) / p * p := hceil_lb
        _ ≤ ((a + (p - 1)) / p + i) * p :=
            Nat.mul_le_mul_right p (Nat.le_add_right _ i)
    · -- Upper bound: ((a+(p-1))/p + i) * p < a + k
      -- ⌈a/p⌉*p < a+p, and (i+1)*p ≤ k, so ⌈a/p⌉*p + i*p < a + (i+1)*p ≤ a + k
      have hik : (i + 1) * p ≤ k :=
        le_trans (Nat.mul_le_mul_right p (by omega : i + 1 ≤ k / p))
          (Nat.div_mul_le_self k p)
      have hceil_ub : (a + (p - 1)) / p * p < a + p := by
        have h1 := Nat.div_add_mod (a + (p - 1)) p
        rw [mul_comm] at h1
        have h2 := Nat.mod_lt (a + (p - 1)) hp_pos
        omega
      calc ((a + (p - 1)) / p + i) * p
          = (a + (p - 1)) / p * p + i * p := by ring
        _ < a + p + i * p := by linarith
        _ = a + (i + 1) * p := by ring
        _ ≤ a + k := by linarith
  -- Conclude: k/p = |range(k/p)| = |image g| ≤ |filter|
  calc k / p = (Finset.range (k / p)).card := (Finset.card_range _).symm
    _ = ((Finset.range (k / p)).image g).card :=
        (Finset.card_image_of_injective _ hg_inj).symm
    _ ≤ ((Finset.Ico a (a + k)).filter (p ∣ ·)).card := Finset.card_le_card hsub

theorem single_prime_upper (p k : ℕ) (hp : Nat.Prime p) :
    coveringFunction {p} k ≤ k / p + 1 := by
  unfold coveringFunction
  apply ciInf_le_of_le ⟨0, fun _ ⟨_, h⟩ => h ▸ Nat.zero_le _⟩ 0
  unfold coveredInInterval
  simp only [Nat.zero_add, Finset.mem_singleton, exists_eq_left]
  -- Multiples of p in Ico 0 k: inject n ↦ n/p into range(k/p+1)
  have h_inj : (Finset.Ico 0 k |>.filter (p ∣ ·) |>.image (· / p)) ⊆ Finset.range (k / p + 1) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  calc (Finset.Ico 0 k |>.filter (p ∣ ·)).card
      ≤ ((Finset.range (k / p + 1)).image (· * p)).card := by
        apply Finset.card_le_card; intro n hn
        rw [Finset.mem_filter, Finset.mem_Ico] at hn
        obtain ⟨⟨_, hn_lt⟩, ⟨m, rfl⟩⟩ := hn
        rw [Finset.mem_image]
        refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), by ring⟩
        exact (Nat.le_div_iff_mul_le hp.pos).mpr (le_of_lt (by linarith))
    _ ≤ (Finset.range (k / p + 1)).card := Finset.card_image_le
    _ = k / p + 1 := Finset.card_range _

/-
## The Inclusion-Exclusion Bound
-/

/-- The expected density is in (0, 1) for a nonempty set of primes ≥ 2. -/
private theorem prod_one_sub_inv_pos (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p) :
    0 < ∏ p ∈ primes, (1 - 1 / (p : ℝ)) := by
  apply Finset.prod_pos
  intro p hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hprime p hp).pos
  rw [sub_pos, div_lt_one hp_pos]
  exact_mod_cast (hprime p hp).one_lt

theorem expectedDensity_pos (primes : Finset ℕ) (hne : primes.Nonempty)
    (hprime : ∀ p ∈ primes, Nat.Prime p) :
    0 < expectedDensity primes := by
  unfold expectedDensity
  simp only [sub_pos]
  -- Each factor (1 - 1/p) satisfies 0 < f < 1 for primes p ≥ 2
  have h_pos : ∀ p ∈ primes, (0 : ℝ) < 1 - 1 / (p : ℝ) := fun p hp => by
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hprime p hp).pos
    have hp1 : (p : ℝ) > 1 := by exact_mod_cast (hprime p hp).one_lt
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp_pos]; linarith
    linarith
  have h_le : ∀ p ∈ primes, 1 - 1 / (p : ℝ) ≤ 1 := fun p hp => by
    linarith [div_pos one_pos (show (0:ℝ) < p from by exact_mod_cast (hprime p hp).pos)]
  -- Split product as f(p₀) * ∏(rest), bound rest ≤ 1, deduce product ≤ f(p₀) < 1
  obtain ⟨p₀, hp₀⟩ := hne
  calc ∏ p ∈ primes, (1 - 1 / (p : ℝ))
      = (1 - 1 / (p₀ : ℝ)) * ∏ p ∈ primes.erase p₀, (1 - 1 / (p : ℝ)) :=
        (Finset.mul_prod_erase _ _ hp₀).symm
    _ ≤ (1 - 1 / (p₀ : ℝ)) := mul_le_of_le_one_right (le_of_lt (h_pos p₀ hp₀))
        (Finset.prod_le_one (fun p hp => le_of_lt (h_pos p (Finset.mem_of_mem_erase hp)))
          (fun p hp => h_le p (Finset.mem_of_mem_erase hp)))
    _ < 1 := by linarith [div_pos one_pos (show (0:ℝ) < p₀ from by exact_mod_cast (hprime p₀ hp₀).pos)]

theorem expectedDensity_lt_one (primes : Finset ℕ) (hne : primes.Nonempty)
    (hprime : ∀ p ∈ primes, Nat.Prime p) :
    expectedDensity primes < 1 := by
  unfold expectedDensity
  linarith [prod_one_sub_inv_pos primes hprime]

/-- For large k, F_k should approach k · expectedDensity.
    This is the "main term" in the estimate. -/
axiom covering_asymptotic (primes : Finset ℕ) (hprime : ∀ p ∈ primes, Nat.Prime p) :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 →
    |(coveringFunction primes k : ℝ) - k * expectedDensity primes| ≤ C

/-
## The α > 2 Regime
-/

/-- When k = αpᵤ with α > 2, the interval contains at least 2 complete
    periods of pᵤ. Erdős-Selfridge found the exact bound for 2 < α < 3.
    Note: The conclusion is trivially true (any ℕ-valued function has a value).
    The mathematical content is the *formula* for exact_val, not its existence. -/
theorem erdos_selfridge_exact (primes : Finset ℕ)
    (_hprime : ∀ p ∈ primes, Nat.Prime p)
    (_hne : primes.Nonempty)
    (_α : ℝ) (_hα_lo : 2 < _α) (_hα_hi : _α < 3)
    (k : ℕ) (_hk : k = Nat.floor (_α * primes.max' _hne)) :
    ∃ exact_val : ℕ, coveringFunction primes k = exact_val :=
  ⟨coveringFunction primes k, rfl⟩

/-- Lower bound: k * (density - 1) ≤ F_k. Trivially true since density < 1
    implies LHS ≤ 0 and F_k ≥ 0. -/
theorem covering_lower_bound (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p)
    (hne : primes.Nonempty) (k : ℕ) :
    k * (expectedDensity primes - 1) ≤ (coveringFunction primes k : ℝ) :=
  le_trans
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
      (by linarith [expectedDensity_lt_one primes hne hprime]))
    (Nat.cast_nonneg _)

/-- Upper bound: F_k ≤ k * density + |primes|. Requires inclusion-exclusion
    with periodicity argument (the average of covered(a,k) over one period
    equals k * density, so the infimum ≤ average). -/
axiom covering_upper_bound (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p)
    (hne : primes.Nonempty) (k : ℕ) :
    (coveringFunction primes k : ℝ) ≤ k * expectedDensity primes + primes.card

/-- For α > 3, F_k is bounded between density bounds. -/
theorem alpha_gt_3_open (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p)
    (hne : primes.Nonempty) :
    ∀ α : ℝ, α > 3 →
    ∀ k : ℕ, k = Nat.floor (α * primes.max' hne) →
    k * (expectedDensity primes - 1) ≤ (coveringFunction primes k : ℝ) ∧
    (coveringFunction primes k : ℝ) ≤ k * expectedDensity primes + primes.card := by
  intro _ _ k _
  exact ⟨covering_lower_bound primes hprime hne k,
         covering_upper_bound primes hprime hne k⟩

/-
## Concrete Examples
-/

/-- For primes {2, 3}, expectedDensity = 1 - (1/2)(2/3) = 2/3.
    In any 6 consecutive integers, exactly 4 are divisible by 2 or 3. -/
theorem density_two_three :
    expectedDensity ({2, 3} : Finset ℕ) = 1 - (1 - 1/2) * (1 - 1/3) := by
  unfold expectedDensity
  norm_num [Finset.prod_pair (show (2:ℕ) ≠ 3 by omega)]

/-- For primes {2, 3, 5}, expectedDensity = 1 - (1/2)(2/3)(4/5) = 11/15. -/
theorem density_two_three_five :
    expectedDensity ({2, 3, 5} : Finset ℕ) = 1 - (1 - 1/2) * (1 - 1/3) * (1 - 1/5) := by
  unfold expectedDensity
  norm_num [Finset.prod_insert (show (2:ℕ) ∉ ({3, 5} : Finset ℕ) by decide),
            Finset.prod_pair (show (3:ℕ) ≠ 5 by omega)]

/-
## Connection to Jacobsthal's Function
-/

/- Jacobsthal's function h(k) asks for the minimal m such that any m
   consecutive integers contain one coprime to a k-prime number.
   F_k is the "dual" question: how many are covered rather than uncovered.

   The key relationship is: uncovered = k - covered.
   Jacobsthal asks for the minimal k such that uncovered = 0.

   If h denotes Jacobsthal's function and n = p₁···pᵤ, then
   F_{h(u)-1}(p₁,...,pᵤ) = h(u) - 1 (all are covered).
   See Erdős #970 for Jacobsthal's function.

   Formally stating this relationship requires defining Jacobsthal's function,
   which is not yet available in this formalization. -/

/-
## Summary

**Erdős Problem #1143** (OPEN):

**Question**: Estimate F_k(p₁,...,pᵤ), the minimum number of integers
in any k-length interval divisible by at least one of the primes p₁,...,pᵤ.

**Known**:
1. For large k, F_k ≈ k · (1 - ∏(1 - 1/pᵢ)) (density approximation)
2. Erdős-Selfridge: exact formula for k = αpᵤ with 2 < α < 3
3. For α > 3: very little known
4. Single prime p: F_k({p}) = ⌊k/p⌋ (exact)
5. Related to Jacobsthal's function (#970)
-/

end Erdos1143
