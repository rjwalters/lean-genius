/-
Erdős Problem #534: Largest Subset with Pairwise Common Divisors

Source: https://erdosproblems.com/534
Status: SOLVED (Ahlswede-Khachatrian, 1996)

Statement:
What is the largest possible subset A ⊆ {1, ..., N} which contains N such that
gcd(a, b) > 1 for all distinct a, b ∈ A?

Answer:
If N = q₁^k₁ ··· qᵣ^kᵣ (where q₁ < ··· < qᵣ are distinct primes), then the maximum
is achieved by, for some 1 ≤ j ≤ r, those integers in [1, N] which are a multiple
of at least one of {2q₁, ..., 2qⱼ, q₁···qⱼ}.

History:
- Problem of Erdős and Graham (1973) [Er73]
- Original conjecture: max is N/p (smallest prime factor) or |{2t : t ≤ N/2, (2t,N) > 1}|
- Ahlswede and Khachatrian found a counterexample (1992)
- Erdős gave a refined conjecture
- Ahlswede and Khachatrian proved the refined conjecture (1996) [AhKh96]

Mathematical Significance:
This is an extremal set theory problem about GCD-intersecting families.
It generalizes questions about sets with prescribed intersection properties.

References:
- Erdős [Er73]: "Problems and results on combinatorial number theory"
- Ahlswede, Khachatrian [AhKh96]: "Sets of integers with pairwise common divisor"
- See also Problem #56
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Divisors

open Nat Finset

namespace Erdos534

/-
## Part I: Basic Definitions

Setting up the framework for GCD-intersecting sets.
-/

/--
A set A is GCD-intersecting if every pair of distinct elements has gcd > 1.
-/
def IsGcdIntersecting (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.gcd a b > 1

/--
A is a valid set for the problem if it's contained in {1, ..., N},
contains N, and is GCD-intersecting.
-/
def IsValidSet (A : Finset ℕ) (N : ℕ) : Prop :=
  (∀ a ∈ A, a ≤ N ∧ a ≥ 1) ∧ N ∈ A ∧ IsGcdIntersecting A

/--
The maximum size of a valid set for N.
-/
noncomputable def maxGcdIntersectingSize (N : ℕ) : ℕ :=
  sSup {A.card | A : Finset ℕ, IsValidSet A N}

/-
## Part II: The Generating Sets

The optimal construction uses specific generating sets based on prime factorization.
-/

/--
The prime factors of N, sorted.
-/
noncomputable def primeFactorsSorted (N : ℕ) : List ℕ :=
  (N.primeFactors.sort (· ≤ ·))

/--
For a given j, the generating set is {2q₁, ..., 2qⱼ, q₁···qⱼ}.
-/
noncomputable def generatingSet (N : ℕ) (j : ℕ) : Finset ℕ :=
  let primes := primeFactorsSorted N
  let firstJ := primes.take j
  let doubled := firstJ.map (· * 2)
  let product := firstJ.foldl (· * ·) 1
  (doubled.toFinset ∪ {product})

/--
The candidate set: integers in [1, N] divisible by at least one element of the generating set.
-/
noncomputable def candidateSet (N : ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n =>
    n ≥ 1 ∧ ∃ g ∈ generatingSet N j, g ∣ n

/-
## Part III: Properties of Candidate Sets

The candidate sets are GCD-intersecting and contain N.
-/

/--
Every candidate set is GCD-intersecting.
-/
axiom candidateSet_is_gcd_intersecting (N j : ℕ) (hN : N ≥ 2) (hj : j ≥ 1) :
    IsGcdIntersecting (candidateSet N j)

/--
Every candidate set contains N (for appropriate j).
-/
axiom candidateSet_contains_N (N j : ℕ) (hN : N ≥ 2) (hj : 1 ≤ j ∧ j ≤ (primeFactorsSorted N).length) :
    N ∈ candidateSet N j

/--
Every candidate set is contained in [1, N].
-/
theorem candidateSet_subset (N j : ℕ) :
    ∀ n ∈ candidateSet N j, n ≤ N ∧ n ≥ 1 := by
  intro n hn
  simp only [candidateSet, Finset.mem_filter, Finset.mem_range] at hn
  constructor
  · omega
  · exact hn.2.1

/-
## Part IV: The Original Conjecture (Disproved)

The original Erdős-Graham conjecture was found to be false.
-/

/--
The original conjecture stated the maximum is either N/p or the count of
{2t : t ≤ N/2 and (2t, N) > 1}.
-/
def originalConjectureValue1 (N : ℕ) : ℕ := N / (N.minFac)

/--
The second value in the original conjecture.
-/
noncomputable def originalConjectureValue2 (N : ℕ) : ℕ :=
  ((Finset.range (N / 2 + 1)).filter fun t =>
    t ≥ 1 ∧ Nat.gcd (2 * t) N > 1).card

/--
**Original Conjecture (Disproved):**
The maximum is either N/minFac(N) or |{2t : t ≤ N/2, gcd(2t, N) > 1}|.
-/
def originalConjecture (N : ℕ) : Prop :=
  maxGcdIntersectingSize N = originalConjectureValue1 N ∨
  maxGcdIntersectingSize N = originalConjectureValue2 N

/--
Ahlswede and Khachatrian found a counterexample to the original conjecture.
-/
axiom original_conjecture_counterexample :
    ∃ N : ℕ, N ≥ 2 ∧ ¬originalConjecture N

/-
## Part V: The Refined Conjecture (Proved)

Erdős gave a refined conjecture after learning of the counterexample.
-/

/--
The maximum value according to the refined conjecture.
-/
noncomputable def refinedConjectureValue (N : ℕ) : ℕ :=
  sSup {(candidateSet N j).card | j : ℕ, 1 ≤ j ∧ j ≤ (primeFactorsSorted N).length}

/--
**Ahlswede-Khachatrian Theorem (1996):**
The maximum size of a GCD-intersecting set A ⊆ {1, ..., N} containing N
is achieved by one of the candidate sets.
-/
axiom ahlswede_khachatrian (N : ℕ) (hN : N ≥ 2) :
    maxGcdIntersectingSize N = refinedConjectureValue N

/--
**Erdős Problem #534: SOLVED**
The main theorem combining all results.
-/
theorem erdos_534 (N : ℕ) (hN : N ≥ 2) :
    maxGcdIntersectingSize N = refinedConjectureValue N :=
  ahlswede_khachatrian N hN

/-
## Part VI: Explicit Characterization

The optimal set has a clean description.
-/

/--
The optimal j* that achieves the maximum.
-/
noncomputable def optimalJ (N : ℕ) : ℕ :=
  Classical.choose (⟨1, by sorry⟩ : ∃ j, 1 ≤ j ∧ j ≤ (primeFactorsSorted N).length ∧
    (candidateSet N j).card = refinedConjectureValue N)

/--
The optimal set is the candidate set for the optimal j.
-/
noncomputable def optimalSet (N : ℕ) : Finset ℕ := candidateSet N (optimalJ N)

/--
The optimal set achieves the maximum.
-/
axiom optimalSet_achieves_max (N : ℕ) (hN : N ≥ 2) :
    (optimalSet N).card = maxGcdIntersectingSize N

/-
## Part VII: Special Cases

Examining specific values of N.
-/

/--
For prime N = p, the maximum is 1 (only {N} works).
-/
axiom prime_case (p : ℕ) (hp : p.Prime) :
    maxGcdIntersectingSize p = 1

/--
For N = p^k (prime power), the maximum is p^(k-1).
-/
axiom prime_power_case (p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    maxGcdIntersectingSize (p ^ k) = p ^ (k - 1)

/--
For N = 2m where m is odd, we can include all even numbers up to N that share a factor with N.
-/
axiom even_case (m : ℕ) (hm : Odd m) (hm2 : m ≥ 3) :
    ∃ A : Finset ℕ, IsValidSet A (2 * m) ∧ A.card ≥ m / 2

/-
## Part VIII: Bounds

Upper and lower bounds on the maximum.
-/

/--
**Upper Bound:**
The maximum is at most N / minFac(N).
-/
axiom upper_bound (N : ℕ) (hN : N ≥ 2) :
    maxGcdIntersectingSize N ≤ N / N.minFac

/--
**Lower Bound:**
For composite N, the maximum is at least 2 (including N and any multiple of its smallest prime factor).
-/
theorem lower_bound (N : ℕ) (hN : N ≥ 4) (hcomp : ¬N.Prime) :
    maxGcdIntersectingSize N ≥ 2 := by
  sorry

/--
The trivial set {N} is always valid.
-/
theorem singleton_valid (N : ℕ) (hN : N ≥ 1) : IsValidSet {N} N := by
  constructor
  · intro a ha
    simp only [Finset.mem_singleton] at ha
    rw [ha]
    exact ⟨le_refl N, hN⟩
  constructor
  · exact Finset.mem_singleton.mpr rfl
  · intro a b ha hb hab
    simp only [Finset.mem_singleton] at ha hb
    rw [ha, hb] at hab
    exact (hab rfl).elim

/-
## Part IX: Connection to Intersecting Families

The problem is related to intersection theory in combinatorics.
-/

/--
A family of sets is intersecting if every pair shares at least one element.
-/
def IsIntersectingFamily {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∀ A B : Finset α, A ∈ F → B ∈ F → A ≠ B → (A ∩ B).Nonempty

/--
GCD-intersecting sets of integers correspond to intersecting families
via the divisor set construction: a ↦ {primes dividing a}.
-/
theorem gcd_to_intersecting (A : Finset ℕ) :
    IsGcdIntersecting A ↔
    IsIntersectingFamily (A.image fun n => n.primeFactors) := by
  sorry

/-
## Part X: Summary

Collecting all key results.
-/

/--
**Summary of Erdős Problem #534:**

1. **Problem:** Find the largest A ⊆ {1, ..., N} containing N with gcd(a,b) > 1 for all a ≠ b.

2. **Original Conjecture:** Max is N/minFac(N) or |{2t : t ≤ N/2, gcd(2t,N) > 1}|.

3. **Counterexample:** Found by Ahlswede-Khachatrian (1992).

4. **Refined Conjecture:** Use generating sets {2q₁, ..., 2qⱼ, q₁···qⱼ}.

5. **Proved:** Ahlswede-Khachatrian (1996).
-/
theorem erdos_534_summary (N : ℕ) (hN : N ≥ 2) :
    -- The maximum is achieved by a candidate set
    maxGcdIntersectingSize N = refinedConjectureValue N ∧
    -- The original conjecture had counterexamples
    (∃ M, M ≥ 2 ∧ ¬originalConjecture M) ∧
    -- The singleton {N} is always valid
    IsValidSet {N} N := by
  constructor
  · exact ahlswede_khachatrian N hN
  constructor
  · exact original_conjecture_counterexample
  · exact singleton_valid N (by omega)

/--
**The Answer:**
For N = q₁^k₁ ··· qᵣ^kᵣ, the maximum is achieved by integers divisible by
at least one of {2q₁, ..., 2qⱼ, q₁···qⱼ} for the optimal j.
-/
theorem erdos_534_answer (N : ℕ) (hN : N ≥ 2) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ (primeFactorsSorted N).length ∧
      maxGcdIntersectingSize N = (candidateSet N j).card := by
  use optimalJ N
  sorry

end Erdos534
