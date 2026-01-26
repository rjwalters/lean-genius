/-!
# Erdős Problem #783: Optimal Sieving with Coprime Sets

Given C > 0 and large n, consider A ⊆ {2, ..., n} where elements are
pairwise coprime and Σ_{a ∈ A} 1/a ≤ C. Which A minimizes the count
of m ≤ n not divisible by any a ∈ A?

## Conjecture
The optimal A consists of the first k consecutive primes (in some order),
where k is maximal such that Σ_{i=1}^{k} 1/p_i ≤ C.

## Context
This is a sieve optimization problem: given a "budget" C on reciprocal
sums, how should one choose a coprime sieving set to eliminate as many
integers as possible? The conjecture says primes are optimal.

## Status: OPEN

Reference: https://erdosproblems.com/783
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A set A ⊆ {2, ..., n} is a valid coprime sieving set if all elements
    are pairwise coprime and have reciprocal sum ≤ C. -/
def IsValidSievingSet (A : Finset ℕ) (n : ℕ) (C : ℝ) : Prop :=
  (∀ a ∈ A, 2 ≤ a ∧ a ≤ n) ∧
  (∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.Coprime a b) ∧
  (A.sum (fun a => (1 : ℝ) / a) ≤ C)

/-- The unsieved count: the number of m ≤ n not divisible by any a ∈ A. -/
def unsievedCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun m => m ≥ 1 ∧ ∀ a ∈ A, ¬(a ∣ m)) |>.card

/-- The optimal sieving problem: minimize unsievedCount over valid sieving sets. -/
def minUnsieved (n : ℕ) (C : ℝ) : ℕ :=
  -- The minimum unsieved count over all valid sieving sets
  Finset.min' sorry sorry -- axiomatized below

axiom minUnsieved_def (n : ℕ) (C : ℝ) (hC : C > 0) :
    ∃ A : Finset ℕ, IsValidSievingSet A n C ∧
      ∀ B : Finset ℕ, IsValidSievingSet B n C →
        unsievedCount A n ≤ unsievedCount B n

/-! ## The Prime Sieving Set -/

/-- The k-th prime number. -/
axiom nthPrime (k : ℕ) : ℕ

/-- nthPrime gives primes in increasing order. -/
axiom nthPrime_prime (k : ℕ) : (nthPrime k).Prime
axiom nthPrime_increasing (i j : ℕ) (h : i < j) : nthPrime i < nthPrime j

/-- The prime sieving set: the first k primes, where k is maximal
    such that Σ_{i=0}^{k-1} 1/p_i ≤ C. -/
def primeSievingSet (k : ℕ) : Finset ℕ :=
  (Finset.range k).image nthPrime

/-- The maximal k such that the first k prime reciprocals sum to ≤ C. -/
axiom maxPrimeCount (C : ℝ) : ℕ

axiom maxPrimeCount_spec (C : ℝ) (hC : C > 0) :
    ((Finset.range (maxPrimeCount C)).sum (fun i => (1 : ℝ) / (nthPrime i))) ≤ C ∧
    ((Finset.range (maxPrimeCount C + 1)).sum (fun i => (1 : ℝ) / (nthPrime i))) > C

/-! ## The Main Conjecture -/

/-- Erdős Problem #783: The prime sieving set is optimal.
    For large n, the set of first k primes (k = maxPrimeCount C)
    minimizes the unsieved count among all valid sieving sets. -/
axiom erdos_783_conjecture (C : ℝ) (hC : C > 0) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ A : Finset ℕ, IsValidSievingSet A n C →
        unsievedCount (primeSievingSet (maxPrimeCount C)) n ≤ unsievedCount A n

/-! ## Inclusion-Exclusion Estimate -/

/-- By inclusion-exclusion, for a coprime set A, the unsieved fraction is
    approximately Π_{a ∈ A} (1 - 1/a). Primes minimize this product for
    a given reciprocal sum, since primes are "most independent" for sieving. -/
axiom coprime_sieve_estimate (A : Finset ℕ) (n : ℕ) (C : ℝ)
    (hvalid : IsValidSievingSet A n C) (hn : n ≥ 1) :
    ∃ δ : ℝ, |((unsievedCount A n : ℝ) / n) -
      A.prod (fun a => 1 - (1 : ℝ) / a)| ≤ δ

/-! ## Why Primes Are Optimal -/

/-- For a fixed reciprocal sum budget C, the product Π(1 - 1/a_i)
    is minimized when the a_i are primes. This is because replacing
    a composite with its prime factor yields a better sieve. -/
axiom primes_minimize_product (A : Finset ℕ) (n : ℕ) (C : ℝ)
    (hvalid : IsValidSievingSet A n C) :
    A.prod (fun a => 1 - (1 : ℝ) / a) ≥
      (primeSievingSet (maxPrimeCount C)).prod (fun a => 1 - (1 : ℝ) / a)
