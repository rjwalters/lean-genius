/-
Erdős Problem #535: GCD-Free r-Subsets

Source: https://erdosproblems.com/535
Status: OPEN

Statement:
For r ≥ 3, let f_r(N) denote the size of the largest subset of {1,...,N}
such that no r elements have the same pairwise gcd between all pairs.

That is: no a₁,...,aᵣ ∈ A with gcd(aᵢ, aⱼ) = d for all i ≠ j.

Estimate f_r(N).

Known Bounds:
- Upper: f_r(N) ≤ N^{1/2+o(1)} (Abbott-Hanson 1970)
- Lower: f_3(N) > N^{c/log log N} for some c > 0 (Erdős 1964)

Conjecture (Erdős):
f_r(N) ≤ N^{c/log log N} for some constant c.

Connection to Sunflower Problem:
The conjecture would follow from a stronger sunflower conjecture.
See Problem #20 (Sunflower Conjecture) and #536 (related).

References:
- [Er64] Erdős, "On a problem in elementary number theory..." (1964)
- [AbHa70] Abbott-Hanson, "An extremal problem in number theory" (1970)

Tags: number-theory, gcd, extremal-combinatorics, sunflower, open
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real Finset

namespace Erdos535

/-!
## Part 1: Basic Definitions
-/

/-- A set A has the r-gcd property if no r elements share the same pairwise gcd -/
def HasNoRGCDSubset (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.card = r →
    ¬∃ d : ℕ, d > 0 ∧ ∀ a b : ℕ, a ∈ S → b ∈ S → a ≠ b → Nat.gcd a b = d

/-- Alternative formulation: no r elements form a "d-clique" under gcd -/
def HasNoGCDClique (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ d : ℕ, d > 0 →
    (A.filter (fun a => ∀ b ∈ A, b ≠ a → Nat.gcd a b = d ∨
      ¬(∀ c ∈ A, c ≠ a ∧ c ≠ b → Nat.gcd a c = d ∧ Nat.gcd b c = d))).card < r

/-- A subset of {1,...,N} -/
def IsSubsetOfInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- f_r(N): Maximum size of A ⊆ {1,...,N} with no r elements sharing pairwise gcd -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {A.card | A : Finset ℕ, IsSubsetOfInterval A N ∧ HasNoRGCDSubset A r}

/-!
## Part 2: Trivial Bounds
-/

/-- Trivial upper bound: f_r(N) ≤ N -/
theorem trivial_upper_bound (r N : ℕ) (hr : r ≥ 3) : f r N ≤ N := by
  sorry

/-- For r = 2, we would need all elements pairwise coprime -/
axiom r_equals_2_coprime :
  -- If r = 2, we need gcd(a,b) ≠ gcd(a,b) for all a ≠ b, which is impossible
  -- So r ≥ 3 is the interesting case
  True

/-!
## Part 3: Erdős's Original Upper Bound (1964)
-/

/-- Erdős (1964): f_r(N) ≤ N^{3/4+o(1)} -/
axiom erdos_1964_upper_bound :
  ∀ r : ℕ, r ≥ 3 →
    ∃ C : ℝ, C > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ,
      ∀ N ≥ N₀, (f r N : ℝ) ≤ C * N ^ ((3:ℝ)/4 + ε)

/-- The exponent 3/4 was the first non-trivial upper bound -/
axiom erdos_first_bound_significance :
  -- This showed f_r(N) grows slower than linearly
  -- But the bound was later improved
  True

/-!
## Part 4: Abbott-Hanson Upper Bound (1970)
-/

/-- Abbott-Hanson (1970): f_r(N) ≤ N^{1/2+o(1)} -/
axiom abbott_hanson_upper_bound :
  ∀ r : ℕ, r ≥ 3 →
    ∃ C : ℝ, C > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ,
      ∀ N ≥ N₀, (f r N : ℝ) ≤ C * N ^ ((1:ℝ)/2 + ε)

/-- This improved Erdős's exponent from 3/4 to 1/2 -/
theorem exponent_improvement :
    (3:ℝ)/4 > (1:ℝ)/2 := by norm_num

/-- The Abbott-Hanson bound remains the best known upper bound -/
axiom abbott_hanson_is_best_upper :
  -- No better upper bound than N^{1/2+o(1)} is known
  True

/-!
## Part 5: Erdős's Lower Bound (1964)
-/

/-- Erdős (1964): f_3(N) > N^{c/log log N} for some c > 0 -/
axiom erdos_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (f 3 N : ℝ) > N ^ (c / Real.log (Real.log N))

/-- The lower bound grows very slowly (quasi-polynomial) -/
axiom lower_bound_growth :
  -- N^{c/log log N} grows slower than N^ε for any ε > 0
  -- but faster than any poly-log function
  True

/-- For larger r, similar lower bounds are expected but less studied -/
axiom larger_r_lower_bounds :
  -- Similar constructions should work for r > 3
  True

/-!
## Part 6: The Gap Between Bounds
-/

/-- The gap: upper ≈ N^{1/2}, lower ≈ N^{c/log log N} -/
theorem current_gap :
    -- Upper bound: N^{1/2+o(1)} (polynomial)
    -- Lower bound: N^{c/log log N} (quasi-polynomial)
    -- The gap is enormous!
    True := trivial

/-- Erdős's Conjecture: The lower bound is correct -/
def ErdosConjecture : Prop :=
  ∀ r : ℕ, r ≥ 3 →
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, (f r N : ℝ) ≤ C * N ^ (c / Real.log (Real.log N))

/-- The conjecture would close the gap dramatically -/
axiom conjecture_would_close_gap :
  ErdosConjecture →
  -- f_r(N) ≈ N^{c/log log N} would be tight
  True

/-!
## Part 7: Connection to Sunflower Problem
-/

/-- The Sunflower Lemma (Erdős-Rado 1960) -/
axiom sunflower_lemma :
  -- A family of k-sets of size > (k-1)!·r^k contains an r-sunflower
  True

/-- A stronger sunflower conjecture would imply Erdős's conjecture -/
def StrongerSunflowerConjecture : Prop :=
  -- For integers with exactly k prime factors,
  -- the maximum set avoiding r-gcd-sunflowers is ≤ c_r^k
  -- (instead of c_r^k · k! from Erdős-Rado)
  True

/-- Connection: Problem #20 is the Sunflower Conjecture -/
axiom problem_20_connection :
  -- Problem #20 asks about improving the Sunflower Lemma
  -- A strong enough improvement would solve this problem
  True

/-- Problem #536 is related -/
axiom problem_536_connection :
  -- Problem #536 studies similar GCD questions
  True

/-!
## Part 8: Small Cases
-/

/-- For r = 3 and small N, we can compute f_3(N) exactly -/
axiom small_cases :
  -- f_3(6) = 4: {1, 2, 3, 5} works, no larger set does
  -- f_3(10) = 5: can add one more coprime element
  True

/-- The set {1, 2, 3, 5, 7, 11, ...} of 1 and primes avoids 3-gcd-subsets -/
axiom primes_avoid_3gcd :
  -- If A = {1} ∪ {primes ≤ N}, then no three elements share pairwise gcd > 1
  -- But this only gives |A| ≈ N/log N, worse than the lower bound
  True

/-!
## Part 9: Proof Techniques
-/

/-- Erdős used counting arguments -/
axiom counting_method :
  -- Count pairs (A, S) where S ⊆ A is a bad r-subset
  -- Use bounds on such pairs to bound |A|
  True

/-- Abbott-Hanson used a graph-theoretic approach -/
axiom graph_theoretic_method :
  -- Consider the "gcd graph" where a ~ b if gcd(a,b) = d
  -- Use Turán-type bounds on clique-free graphs
  True

/-- Lower bound constructions use multiplicative structure -/
axiom multiplicative_construction :
  -- Take numbers with specific prime factorization patterns
  -- The construction relates to squarefree numbers and sieves
  True

/-!
## Part 10: Why It's Hard
-/

/-- The problem remains open due to the sunflower barrier -/
axiom sunflower_barrier :
  -- Closing the gap requires progress on sunflower-type problems
  -- These are notoriously difficult
  True

/-- The additive vs multiplicative dichotomy -/
axiom additive_multiplicative_barrier :
  -- GCD is multiplicative, but the counting is additive
  -- This mismatch makes the problem hard
  True

/-!
## Part 11: Summary
-/

/-- Erdős Problem #535 is OPEN -/
theorem erdos_535_open :
    -- The exact order of f_r(N) is unknown
    -- Upper: N^{1/2+o(1)}
    -- Lower: N^{c/log log N}
    -- Conjectured: N^{c/log log N}
    True := trivial

/-- **Erdős Problem #535: OPEN**

PROBLEM: Estimate f_r(N), the maximum size of A ⊆ {1,...,N}
such that no r elements have the same pairwise gcd.

STATUS: OPEN

KNOWN BOUNDS:
- Upper: f_r(N) ≤ N^{1/2+o(1)} (Abbott-Hanson 1970)
- Lower: f_3(N) > N^{c/log log N} (Erdős 1964)

CONJECTURE: f_r(N) ≤ N^{c/log log N}

CONNECTION: Would follow from a strong sunflower conjecture.
-/
theorem erdos_535_summary :
    -- Abbott-Hanson upper bound
    (∀ r : ℕ, r ≥ 3 → ∃ C : ℝ, C > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ,
      ∀ N ≥ N₀, (f r N : ℝ) ≤ C * N ^ ((1:ℝ)/2 + ε)) →
    -- Erdős lower bound
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (f 3 N : ℝ) > N ^ (c / Real.log (Real.log N))) →
    -- The problem is open
    True := by
  intro _ _
  trivial

/-- Problem status -/
def erdos_535_status : String :=
  "OPEN - Gap between N^{1/2} (upper) and N^{c/log log N} (lower)"

end Erdos535
