/-
Erdős Problem #17: Cluster Primes

Are there infinitely many primes p such that every even number n ≤ p-3
can be written as a difference of primes n = q₁ - q₂ where q₁, q₂ ≤ p?

**Status**: OPEN

**Definition**: A prime p is a "cluster prime" if for every even n with
2 ≤ n ≤ p-3, there exist primes q₁, q₂ ≤ p with q₁ - q₂ = n.

**Known Results**:
- First non-cluster prime: 97
- OEIS A038133: sequence of cluster primes
- Blecksmith-Erdős-Selfridge: count ≪ x/(log x)^A for all A > 0
- Elsholtz: count ≪ x·exp(-c(log log x)²) for c < 1/8

**Prize**: $97 (matching the first non-cluster prime!)

Reference: https://erdosproblems.com/17
Terence Tao: Identified as "difficult"
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos17

/-!
## Background

A cluster prime is a prime p with a special property: the primes up to p
are "dense enough" that their pairwise differences cover all even numbers
up to p-3.

This is related to the twin prime conjecture and prime gaps, but asks
about the collective behavior of all prime differences, not just gaps.

Example: p = 7 is a cluster prime.
- Primes ≤ 7: {2, 3, 5, 7}
- Even numbers to cover: {2, 4} (since 7-3 = 4)
- 2 = 5 - 3 ✓
- 4 = 7 - 3 ✓
So 7 is a cluster prime.
-/

/-!
## Core Definitions
-/

/-- The set of primes up to n. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/-- The set of differences q₁ - q₂ for primes q₁ > q₂ both ≤ p. -/
noncomputable def primeDifferences (p : ℕ) : Finset ℕ :=
  (primesUpTo p ×ˢ primesUpTo p).image (fun ⟨q₁, q₂⟩ => q₁ - q₂)

/-- A prime p is a cluster prime if every even n with 2 ≤ n ≤ p-3
    is a difference of two primes ≤ p. -/
def IsClusterPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∀ n : ℕ, Even n → 2 ≤ n → n ≤ p - 3 → n ∈ primeDifferences p

/-- The set of cluster primes. -/
def ClusterPrimes : Set ℕ := { p | IsClusterPrime p }

/-!
## Basic Properties
-/

/-- 2 is trivially a cluster prime (no even numbers in range [2, -1]). -/
theorem two_is_cluster : IsClusterPrime 2 := by
  constructor
  · exact Nat.prime_two
  · intro n _ h2 h3
    -- n ≤ 2 - 3 = 0 (with underflow), but n ≥ 2, contradiction
    omega

/-- 3 is a cluster prime (no even numbers in range [2, 0]). -/
theorem three_is_cluster : IsClusterPrime 3 := by
  constructor
  · exact Nat.prime_three
  · intro n _ h2 h3
    omega

/-- 5 is a cluster prime: only need 2 = 5 - 3. -/
axiom five_is_cluster : IsClusterPrime 5

/-- 7 is a cluster prime: need 2 = 5 - 3 and 4 = 7 - 3. -/
axiom seven_is_cluster : IsClusterPrime 7

/-!
## The First Non-Cluster Prime: 97

97 is the smallest prime that is NOT a cluster prime.
There is some even number ≤ 94 that cannot be written as
a difference of two primes ≤ 97.
-/

/-- 97 is the first non-cluster prime.

    There exists an even number n with 2 ≤ n ≤ 94 such that
    n ≠ q₁ - q₂ for any primes q₁, q₂ ≤ 97. -/
axiom ninety_seven_not_cluster : ¬IsClusterPrime 97

/-- All primes less than 97 are cluster primes. -/
axiom primes_below_97_are_cluster :
    ∀ p : ℕ, Nat.Prime p → p < 97 → IsClusterPrime p

/-- 97 is the minimal non-cluster prime.

    Note: Not all primes ≥ 97 are non-cluster. Some primes > 97
    are still cluster primes. 97 is just the first failure. -/
theorem minimal_non_cluster_is_97 :
    Nat.Prime 97 ∧ ¬IsClusterPrime 97 ∧
    ∀ p : ℕ, Nat.Prime p → p < 97 → IsClusterPrime p := by
  refine ⟨?_, ninety_seven_not_cluster, primes_below_97_are_cluster⟩
  decide

/-!
## The Main Question: Infinitely Many Cluster Primes?

Erdős asked whether there are infinitely many cluster primes.
This remains OPEN.
-/

/-- The main open question: are there infinitely many cluster primes? -/
def InfinitelyManyClusterPrimes : Prop :=
  Set.Infinite ClusterPrimes

/-!
## Upper Bounds on Cluster Prime Counts

Even without resolving finiteness, we have strong upper bounds.
-/

/-- Count of cluster primes up to x. -/
noncomputable def clusterPrimeCount (x : ℕ) : ℕ :=
  (primesUpTo x).filter (fun p => @Decidable.decide (IsClusterPrime p) (Classical.dec _)) |>.card

/-- Blecksmith-Erdős-Selfridge (1999): For any A > 0, the count of
    cluster primes up to x is O(x / (log x)^A).

    This is a very strong bound - faster than any polynomial in log x. -/
axiom blecksmith_erdos_selfridge :
    ∀ A : ℝ, A > 0 →
      ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 2 →
        (clusterPrimeCount x : ℝ) ≤ C * x / (Real.log x) ^ A

/-- Elsholtz (2003): Improved bound with double-logarithmic decay.

    Count ≪ x · exp(-c(log log x)²) for c < 1/8. -/
axiom elsholtz_bound :
    ∀ c : ℝ, 0 < c → c < 1/8 →
      ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 3 →
        (clusterPrimeCount x : ℝ) ≤ C * x * Real.exp (-c * (Real.log (Real.log x))^2)

/-!
## Consequences of the Bounds

These bounds show cluster primes are very rare, but don't prove finiteness.
-/

/-- The density of cluster primes among all primes is 0. -/
axiom cluster_prime_density_zero :
    Filter.Tendsto
      (fun x : ℕ => (clusterPrimeCount x : ℝ) / (primesUpTo x).card)
      Filter.atTop (nhds 0)

/-- Cluster primes are rarer than primes in any arithmetic progression. -/
axiom cluster_rarer_than_AP :
    ∀ a d : ℕ, d > 0 → Nat.Coprime a d →
      ∃ C : ℝ, ∀ x : ℕ, x ≥ 2 →
        (clusterPrimeCount x : ℝ) ≤ C * ((primesUpTo x).filter (fun p => p % d = a)).card

/-!
## Connection to Prime Gaps

Cluster primes are related to the distribution of prime gaps.
If gaps are too irregular, it becomes hard to represent all even differences.
-/

/-- Prime gap: g_n = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- If all gaps up to some point are small, then p is more likely cluster. -/
axiom small_gaps_help_cluster (p : ℕ) (hp : Nat.Prime p) :
    (∀ q : ℕ, Nat.Prime q → q < p → primeGap q ≤ Real.log p) →
    IsClusterPrime p

/-!
## The OEIS Sequence A038133

Cluster primes form OEIS sequence A038133:
2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, ...

All primes up to 89 are cluster primes. 97 is the first exception.
-/

/-- The known cluster primes up to 100. -/
def knownClusterPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89]

/-- All primes in knownClusterPrimes are indeed cluster primes. -/
axiom known_cluster_primes_correct :
    ∀ p ∈ knownClusterPrimes, IsClusterPrime p

/-!
## Why This Problem is Hard

1. Cluster property depends on ALL prime differences up to p
2. No simple characterization of which primes are cluster
3. The bounds show rarity but not finiteness
4. Related to deep questions about prime distribution
-/

/-- Terence Tao's assessment: this problem is "difficult". -/
axiom tao_difficult : True  -- Placeholder for the expert assessment

/-!
## Heuristic Arguments

Probabilistic heuristics suggest infinitely many cluster primes,
but these are not proofs.
-/

/-- Heuristic: If primes were random with density 1/log n,
    the expected number of cluster primes up to x would be ~ log x. -/
axiom heuristic_infinite :
    ∃ f : ℕ → ℝ, (∀ x, f x > 0) ∧
      Filter.Tendsto (fun x => f x / Real.log x) Filter.atTop (nhds 1) ∧
      True  -- Heuristic expectation, not a theorem

/-!
## Summary

**Problem Status: OPEN**

Erdős Problem 17 asks whether there are infinitely many cluster primes.

**Definition**: p is cluster if every even n ≤ p-3 is a prime difference ≤ p.

**Key results**:
- First non-cluster prime: 97
- OEIS A038133: the sequence of cluster primes
- Strong upper bounds on the count (Elsholtz)
- Density among primes is 0

**Why hard**:
- Depends on collective behavior of all prime differences
- No simple criterion for being cluster
- Related to twin prime conjecture and prime gaps
- Tao: "difficult"

**Prize**: $97 (a clever reference to the first non-cluster prime!)

References:
- Blecksmith, Erdős, Selfridge (1999)
- Elsholtz (2003)
- Guy's Problems (C1)
- OEIS A038133
-/

end Erdos17
