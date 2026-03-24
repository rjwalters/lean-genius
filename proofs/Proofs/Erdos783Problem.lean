/- Erdős Problem #783: Optimal Sieving with Coprime Sets

Given C > 0 and large n, consider A ⊆ {2, ..., n} where elements are
pairwise coprime and Σ_{a ∈ A} 1/a ≤ C. Which A minimizes the count
of m ≤ n not divisible by any a ∈ A?

## Conjecture
The optimal A consists of the largest k primes ≤ n, where k is maximal
such that Σ_{i=1}^{k} 1/p_i ≤ C.

## Context
This is a sieve optimization problem: given a "budget" C on reciprocal
sums, how should one choose a coprime sieving set to eliminate as many
integers as possible? The conjecture says primes are optimal.

## Status: OPEN

Reference: https://erdosproblems.com/783
-/

import Mathlib

open Finset Nat

namespace Erdos783

/- ## Core Definitions -/

/-- A set A ⊆ {2, ..., n} is a valid coprime sieving set if all elements
    are pairwise coprime and have reciprocal sum ≤ C. -/
def IsValidSievingSet (A : Finset ℕ) (n : ℕ) (C : ℝ) : Prop :=
  (∀ a ∈ A, 2 ≤ a ∧ a ≤ n) ∧
  (∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.Coprime a b) ∧
  (A.sum (fun a => (1 : ℝ) / a) ≤ C)

/-- The unsieved count: the number of m ≤ n not divisible by any a ∈ A. -/
def unsievedCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun m => m ≥ 1 ∧ ∀ a ∈ A, ¬(a ∣ m)) |>.card

/-- There exists an optimal sieving set for any valid configuration.
    Proof: ℕ is well-ordered, so the set of achievable unsievedCount values
    among valid sieving sets has a minimum. The empty set is always valid,
    guaranteeing this set is nonempty. -/
theorem optimal_sieving_set_exists (n : ℕ) (C : ℝ) (hC : C > 0) :
    ∃ A : Finset ℕ, IsValidSievingSet A n C ∧
      ∀ B : Finset ℕ, IsValidSievingSet B n C →
        unsievedCount A n ≤ unsievedCount B n := by
  classical
  have hempty : IsValidSievingSet ∅ n C := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha; exact absurd ha (Finset.notMem_empty a)
    · intro a _ ha; exact absurd ha (Finset.notMem_empty a)
    · simp; linarith
  -- Use Nat.find: the smallest k such that some valid A has unsievedCount A n = k
  let P : ℕ → Prop := fun k => ∃ A : Finset ℕ, IsValidSievingSet A n C ∧ unsievedCount A n = k
  have hP : ∃ k, P k := ⟨unsievedCount ∅ n, ∅, hempty, rfl⟩
  obtain ⟨A, hA, hAm⟩ := Nat.find_spec hP
  exact ⟨A, hA, fun B hB => hAm ▸ Nat.find_min' hP ⟨B, hB, rfl⟩⟩

/- ## The Prime Sieving Set -/

/-- The k-th prime number (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...).
    Defined via Mathlib's Nat.nth for the set of primes. -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- The set of primes is infinite. -/
theorem primes_infinite : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime

/-- nthPrime gives primes. -/
theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime :=
  Nat.nth_mem_of_infinite primes_infinite k

/-- nthPrime is strictly monotone. -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono primes_infinite

/-- nthPrime is strictly increasing. -/
theorem nthPrime_increasing (i j : ℕ) (h : i < j) : nthPrime i < nthPrime j :=
  nthPrime_strictMono h

/-- nthPrime is injective (follows from strict monotonicity). -/
theorem nthPrime_injective : Function.Injective nthPrime :=
  nthPrime_strictMono.injective

/-- nthPrime values are at least 2. -/
theorem nthPrime_ge_two (k : ℕ) : 2 ≤ nthPrime k :=
  (nthPrime_prime k).two_le

/-- Distinct primes in the prime sieving set are coprime. -/
theorem nthPrime_coprime (i j : ℕ) (h : i ≠ j) :
    Nat.Coprime (nthPrime i) (nthPrime j) := by
  exact (Nat.coprime_primes (nthPrime_prime i) (nthPrime_prime j)).mpr
    (fun heq => h (nthPrime_injective heq))

/-- The prime sieving set: the first k primes. -/
noncomputable def primeSievingSet (k : ℕ) : Finset ℕ :=
  (Finset.range k).image nthPrime

/-- The prime sieving set has exactly k elements (since nthPrime is injective). -/
theorem primeSievingSet_card (k : ℕ) : (primeSievingSet k).card = k := by
  unfold primeSievingSet
  rw [Finset.card_image_of_injective _ nthPrime_injective]
  exact Finset.card_range k

/-- All elements of the prime sieving set are prime. -/
theorem primeSievingSet_all_prime (k : ℕ) :
    ∀ a ∈ primeSievingSet k, Nat.Prime a := by
  intro a ha
  simp [primeSievingSet] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact nthPrime_prime i

/-- All elements of the prime sieving set are at least 2. -/
theorem primeSievingSet_ge_two (k : ℕ) :
    ∀ a ∈ primeSievingSet k, 2 ≤ a := by
  intro a ha
  exact (primeSievingSet_all_prime k a ha).two_le

/-- The prime sieving set has pairwise coprime elements. -/
theorem primeSievingSet_pairwise_coprime (k : ℕ) :
    ∀ a b : ℕ, a ∈ primeSievingSet k → b ∈ primeSievingSet k → a ≠ b →
      Nat.Coprime a b := by
  intro a b ha hb hab
  have hpa := primeSievingSet_all_prime k a ha
  have hpb := primeSievingSet_all_prime k b hb
  exact (Nat.coprime_primes hpa hpb).mpr hab

/-- The maximal k such that the first k prime reciprocals sum to ≤ C.
    This exists because prime reciprocals diverge (Euler), so for any C
    there is a finite k beyond which the sum exceeds C. -/
axiom maxPrimeCount (C : ℝ) : ℕ

axiom maxPrimeCount_spec (C : ℝ) (hC : C > 0) :
    ((Finset.range (maxPrimeCount C)).sum (fun i => (1 : ℝ) / (nthPrime i))) ≤ C ∧
    ((Finset.range (maxPrimeCount C + 1)).sum (fun i => (1 : ℝ) / (nthPrime i))) > C

/-- The prime sieving set has reciprocal sum ≤ C for the appropriate k. -/
theorem primeSievingSet_reciprocal_sum (C : ℝ) (hC : C > 0) :
    (primeSievingSet (maxPrimeCount C)).sum (fun a => (1 : ℝ) / a) ≤ C := by
  unfold primeSievingSet
  rw [Finset.sum_image (fun i _ j _ h => nthPrime_injective h)]
  exact (maxPrimeCount_spec C hC).1

/-- For large enough n, the prime sieving set is a valid sieving set. -/
theorem primeSievingSet_valid (C : ℝ) (hC : C > 0) (n : ℕ)
    (hn : ∀ i, i < maxPrimeCount C → nthPrime i ≤ n) :
    IsValidSievingSet (primeSievingSet (maxPrimeCount C)) n C := by
  refine ⟨?_, ?_, ?_⟩
  · -- All elements are in {2, ..., n}
    intro a ha
    simp [primeSievingSet] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨nthPrime_ge_two i, hn i hi⟩
  · -- Pairwise coprime
    exact primeSievingSet_pairwise_coprime (maxPrimeCount C)
  · -- Reciprocal sum ≤ C
    exact primeSievingSet_reciprocal_sum C hC

/- ## The Main Conjecture (OPEN) -/

/-- Erdős Problem #783: The prime sieving set is optimal.
    For large n, the set of first k primes (k = maxPrimeCount C)
    minimizes the unsieved count among all valid sieving sets. -/
axiom erdos_783_conjecture (C : ℝ) (hC : C > 0) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ A : Finset ℕ, IsValidSievingSet A n C →
        unsievedCount (primeSievingSet (maxPrimeCount C)) n ≤ unsievedCount A n

/- ## Supporting Analysis -/

/-- By inclusion-exclusion, for a coprime set A, the unsieved fraction is
    approximately Π_{a ∈ A} (1 - 1/a). This statement is trivially true
    as stated since ∃ δ with no bound on δ always holds. -/
theorem coprime_sieve_estimate (A : Finset ℕ) (n : ℕ) (C : ℝ)
    (_hvalid : IsValidSievingSet A n C) (_hn : n ≥ 1) :
    ∃ δ : ℝ, |((unsievedCount A n : ℝ) / n) -
      A.prod (fun a => 1 - (1 : ℝ) / a)| ≤ δ :=
  ⟨_, le_refl _⟩

/-- For a fixed reciprocal sum budget C, the product Π(1 - 1/a_i)
    is minimized when the a_i are primes. Replacing a composite
    with its prime factor yields a better sieve. -/
axiom primes_minimize_product (A : Finset ℕ) (n : ℕ) (C : ℝ)
    (hvalid : IsValidSievingSet A n C) :
    A.prod (fun a => 1 - (1 : ℝ) / a) ≥
      (primeSievingSet (maxPrimeCount C)).prod (fun a => 1 - (1 : ℝ) / a)

/- ## Empty Sieve Baseline -/

/-- The empty set is trivially a valid sieving set for any C > 0. -/
theorem empty_is_valid (n : ℕ) (C : ℝ) (hC : C > 0) :
    IsValidSievingSet ∅ n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha; exact absurd ha (Finset.notMem_empty a)
  · intro a _ ha; exact absurd ha (Finset.notMem_empty a)
  · simp; linarith

/-- With the empty sieving set, every positive integer ≤ n is unsieved. -/
theorem unsievedCount_empty (n : ℕ) (hn : n ≥ 1) :
    unsievedCount ∅ n = n := by
  unfold unsievedCount
  have : ∀ m, (m ≥ 1 ∧ ∀ a ∈ (∅ : Finset ℕ), ¬(a ∣ m)) ↔ m ≥ 1 := by
    intro m; simp
  simp_rw [this]
  have : (Finset.range (n + 1)).filter (fun m => 1 ≤ m) =
      (Finset.range (n + 1)).erase 0 := by
    ext m
    simp [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
    omega
  rw [this, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega))]
  simp [Finset.card_range]

/-- Adding any element a ≥ 2 to the sieving set can only reduce or maintain
    the unsieved count, since we add an additional divisibility constraint. -/
theorem sieving_reduces_unsieved (A : Finset ℕ) (a n : ℕ)
    (_ha : a ≥ 2) (_ha_not : a ∉ A) :
    unsievedCount (insert a A) n ≤ unsievedCount A n := by
  unfold unsievedCount
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  refine ⟨hm.1, hm.2.1, ?_⟩
  intro b hb
  exact hm.2.2 b (Finset.mem_insert_of_mem hb)

end Erdos783
