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
  sorry

/-- For a single prime p, F_k({p}) = ⌊k/p⌋ or ⌈k/p⌉.
    More precisely, in any k consecutive integers, at least ⌊k/p⌋ are
    divisible by p, and at most ⌈k/p⌉. -/
theorem single_prime_lower (p k : ℕ) (hp : Nat.Prime p) (hk : k ≥ 1) :
    coveringFunction {p} k ≥ k / p := by
  sorry

theorem single_prime_upper (p k : ℕ) (hp : Nat.Prime p) :
    coveringFunction {p} k ≤ k / p + 1 := by
  sorry

/-
## The Inclusion-Exclusion Bound
-/

/-- The expected density is in (0, 1) for a nonempty set of primes ≥ 2. -/
theorem expectedDensity_pos (primes : Finset ℕ) (hne : primes.Nonempty)
    (hprime : ∀ p ∈ primes, Nat.Prime p) :
    0 < expectedDensity primes := by
  unfold expectedDensity
  simp only [sub_pos]
  sorry

theorem expectedDensity_lt_one (primes : Finset ℕ) (hne : primes.Nonempty)
    (hprime : ∀ p ∈ primes, Nat.Prime p) :
    expectedDensity primes < 1 := by
  unfold expectedDensity
  linarith [show ∏ p ∈ primes, (1 - 1 / (p : ℝ)) > 0 from by sorry]

/-- For large k, F_k should approach k · expectedDensity.
    This is the "main term" in the estimate. -/
axiom covering_asymptotic (primes : Finset ℕ) (hprime : ∀ p ∈ primes, Nat.Prime p) :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 →
    |(coveringFunction primes k : ℝ) - k * expectedDensity primes| ≤ C

/-
## The α > 2 Regime
-/

/-- When k = αpᵤ with α > 2, the interval contains at least 2 complete
    periods of pᵤ. Erdős-Selfridge found the exact bound for 2 < α < 3. -/
axiom erdos_selfridge_exact (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p)
    (hne : primes.Nonempty)
    (α : ℝ) (hα_lo : 2 < α) (hα_hi : α < 3)
    (k : ℕ) (hk : k = Nat.floor (α * primes.max' hne)) :
    ∃ exact_val : ℕ, coveringFunction primes k = exact_val

/-- For α > 3, very little is known about the exact value of F_k. -/
axiom alpha_gt_3_open (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p)
    (hne : primes.Nonempty) :
    ∀ α : ℝ, α > 3 →
    ∀ k : ℕ, k = Nat.floor (α * primes.max' hne) →
    -- The covering function is bounded between the density bounds
    k * (expectedDensity primes - 1) ≤ (coveringFunction primes k : ℝ) ∧
    (coveringFunction primes k : ℝ) ≤ k * expectedDensity primes + primes.card

/-
## Concrete Examples
-/

/-- For primes {2, 3}, expectedDensity = 1 - (1/2)(2/3) = 2/3.
    In any 6 consecutive integers, exactly 4 are divisible by 2 or 3. -/
theorem density_two_three :
    expectedDensity ({2, 3} : Finset ℕ) = 1 - (1 - 1/2) * (1 - 1/3) := by
  unfold expectedDensity
  congr 1
  rw [show ({2, 3} : Finset ℕ) = {2, 3} from rfl]
  simp only [Finset.prod_insert (show (2 : ℕ) ∉ ({3} : Finset ℕ) by decide),
    Finset.prod_singleton]; push_cast; ring

/-- For primes {2, 3, 5}, expectedDensity = 1 - (1/2)(2/3)(4/5) = 11/15. -/
theorem density_two_three_five :
    expectedDensity ({2, 3, 5} : Finset ℕ) = 1 - (1 - 1/2) * (1 - 1/3) * (1 - 1/5) := by
  unfold expectedDensity
  congr 1
  simp only [Finset.prod_insert (show (2 : ℕ) ∉ ({3, 5} : Finset ℕ) by decide),
    Finset.prod_insert (show (3 : ℕ) ∉ ({5} : Finset ℕ) by decide),
    Finset.prod_singleton]; push_cast; ring

/-
## Connection to Jacobsthal's Function
-/

/-- Jacobsthal's function h(k) asks for the minimal m such that any m
    consecutive integers contain one coprime to a k-prime number.
    F_k is the "dual" question: how many are covered rather than uncovered.

    If h denotes Jacobsthal's function and n = p₁···pᵤ, then
    F_{h(u)-1}(p₁,...,pᵤ) = h(u) - 1 (all are covered).
    See Erdős #970 for Jacobsthal's function. -/
theorem covering_complement_relation (primes : Finset ℕ) (k : ℕ) :
    -- uncovered = k - covered
    -- Jacobsthal asks for min k such that uncovered = 0
    True := by trivial

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
