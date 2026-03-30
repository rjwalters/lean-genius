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

## Axiom Reduction
maxPrimeCount and maxPrimeCount_spec were originally axioms (4 total).
Now proved from Mathlib's prime reciprocal divergence, reducing to 2 axioms.

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

/- ## Constructing maxPrimeCount from prime reciprocal divergence

The following lemmas prove that the partial sums of prime reciprocals
are unbounded (a consequence of Euler's theorem, available in Mathlib as
`not_summable_one_div_on_primes`). This lets us construct `maxPrimeCount`
via `Nat.find` instead of axiomatizing it. -/

/-- Primes up to n (inclusive), used locally for the divergence bridge. -/
private noncomputable def primesBelow (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/-- The sum of prime reciprocals diverges: for any C > 0, there exists N
    such that the sum of 1/p over primes p ≤ N exceeds C.
    Proved from Mathlib's `not_summable_one_div_on_primes`. -/
private lemma primeReciprocalSumDiverges :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, C < (primesBelow N).sum (fun p => (1 : ℝ) / p) := by
  intro C _
  have hns := not_summable_one_div_on_primes
  have hnn : ∀ i, 0 ≤ ({p : ℕ | p.Prime}.indicator fun n : ℕ => (1 : ℝ) / ↑n) i :=
    fun i => Set.indicator_apply_nonneg (fun _ => by positivity)
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hnn] at hns
  rw [Filter.tendsto_atTop_atTop] at hns
  obtain ⟨N, hN⟩ := hns (C + 1)
  use N
  have h_bound := hN N le_rfl
  have h_ind_eq : ∀ x, ({p : ℕ | p.Prime}.indicator fun n : ℕ => (1 : ℝ) / ↑n) x =
      if x.Prime then (1 : ℝ) / ↑x else 0 := fun x => by
    simp [Set.indicator_apply]
  simp_rw [h_ind_eq, ← Finset.sum_filter] at h_bound
  have h_sub : (Finset.range N).filter Nat.Prime ⊆ primesBelow N := by
    intro p hp
    simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have h_le := Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
  linarith

/-- The number of primes below p is strictly less than p for any prime p,
    since {0, ..., p-1} contains non-primes (at least 0 and 1). -/
private lemma count_primes_lt (p : ℕ) (hp : Nat.Prime p) :
    Nat.count Nat.Prime p < p := by
  rw [Nat.count_eq_card_filter_range, ← Finset.card_range p]
  by_contra h
  push_neg at h
  have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) h
  have h0 : 0 ∈ (Finset.range p).filter Nat.Prime := by
    rw [heq]; exact Finset.mem_range.mpr hp.pos
  exact Nat.not_prime_zero (Finset.mem_filter.mp h0).2

/-- Every prime ≤ N is among the first N values of nthPrime.
    Uses `Nat.nth_count`: for prime p, nthPrime(count(p)) = p,
    and count(p) < p ≤ N. -/
private lemma primesBelow_subset_primeSievingSet (N : ℕ) :
    primesBelow N ⊆ primeSievingSet N := by
  intro p hp
  simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at hp
  simp only [primeSievingSet, Finset.mem_image, Finset.mem_range]
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · calc Nat.count Nat.Prime p < p := count_primes_lt p hp.2
      _ ≤ N := by omega
  · exact Nat.nth_count hp.2

/-- The partial sums ∑_{i<k} 1/nthPrime(i) are unbounded.
    Bridges from primesBelow-based divergence to nthPrime-indexed sums
    via the subset relation primesBelow N ⊆ primeSievingSet N. -/
private lemma primeSumUnbounded (C : ℝ) (hC : 0 < C) :
    ∃ k, C < (Finset.range k).sum (fun i => (1 : ℝ) / (nthPrime i)) := by
  obtain ⟨N, hN⟩ := primeReciprocalSumDiverges C hC
  exact ⟨N, by
    calc C < (primesBelow N).sum (fun p => (1 : ℝ) / p) := hN
      _ ≤ (primeSievingSet N).sum (fun p => (1 : ℝ) / p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (primesBelow_subset_primeSievingSet N)
            (fun _ _ _ => by positivity)
      _ = (Finset.range N).sum (fun i => (1 : ℝ) / (nthPrime i)) := by
          unfold primeSievingSet
          rw [Finset.sum_image (fun i _ j _ h => nthPrime_injective h)]⟩

/-- Shifted version: for any C > 0, ∃ k with sum of first k+1 prime reciprocals > C. -/
private lemma exists_prime_sum_exceeds (C : ℝ) (hC : 0 < C) :
    ∃ k, (Finset.range (k + 1)).sum (fun i => (1 : ℝ) / (nthPrime i)) > C := by
  obtain ⟨m, hm⟩ := primeSumUnbounded C hC
  cases m with
  | zero => simp at hm; linarith
  | succ n => exact ⟨n, hm⟩

/-- The maximal k such that the first k prime reciprocals sum to ≤ C.
    Constructed from the divergence of ∑1/p via `Nat.find`, replacing
    the former axiom. For C ≤ 0, returns 0 (spec only used with C > 0). -/
noncomputable def maxPrimeCount (C : ℝ) : ℕ :=
  if h : C > 0 then Nat.find (exists_prime_sum_exceeds C h) else 0

/-- The maximal prime count satisfies: sum of first k ≤ C, sum of first k+1 > C.
    Proved from `Nat.find_spec` and `Nat.find_min`. -/
theorem maxPrimeCount_spec (C : ℝ) (hC : C > 0) :
    ((Finset.range (maxPrimeCount C)).sum (fun i => (1 : ℝ) / (nthPrime i))) ≤ C ∧
    ((Finset.range (maxPrimeCount C + 1)).sum (fun i => (1 : ℝ) / (nthPrime i))) > C := by
  have hdef : maxPrimeCount C = Nat.find (exists_prime_sum_exceeds C hC) := by
    simp only [maxPrimeCount, dif_pos hC]
  rw [hdef]
  constructor
  · -- Sum of first k₀ terms ≤ C (from minimality of Nat.find)
    set k₀ := Nat.find (exists_prime_sum_exceeds C hC)
    cases k₀ with
    | zero => simp; linarith
    | succ n =>
      have h_min := Nat.find_min (exists_prime_sum_exceeds C hC) (Nat.lt_succ_self n)
      push_neg at h_min
      exact h_min
  · -- Sum of first k₀ + 1 terms > C (from Nat.find_spec)
    exact Nat.find_spec (exists_prime_sum_exceeds C hC)

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
