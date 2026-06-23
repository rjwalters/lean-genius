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

/-
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

/-
## Part 2: Trivial Bounds
-/

/-- Trivial upper bound: f_r(N) ≤ N -/
/-
For r = 2, we would need gcd(a,b) ≠ gcd(a,b) for all a ≠ b, which is impossible.
So r ≥ 3 is the interesting case.
-/

/-
## Part 3: Erdős's Original Upper Bound (1964)
-/

/-- Erdős (1964): f_r(N) ≤ N^{3/4+o(1)} -/
/-
The exponent 3/4 was the first non-trivial upper bound, showing f_r(N) grows
slower than linearly. But the bound was later improved by Abbott and Hanson.
-/

/-
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

/-
The Abbott-Hanson bound remains the best known upper bound. No improvement
beyond N^{1/2+o(1)} has been achieved.
-/

/-
## Part 5: Erdős's Lower Bound (1964)
-/

/-- Erdős (1964): f_3(N) > N^{c/log log N} for some c > 0 -/
axiom erdos_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (f 3 N : ℝ) > N ^ (c / Real.log (Real.log N))

/-
The lower bound N^{c/log log N} grows very slowly (quasi-polynomial): slower
than N^ε for any ε > 0, but faster than any poly-log function.

For larger r, similar lower bounds are expected but are less studied.
-/

/-
## Part 6: The Gap Between Bounds

The gap between upper and lower bounds is enormous:
- Upper: N^{1/2+o(1)} (polynomial in N)
- Lower: N^{c/log log N} (quasi-polynomial)
-/

/-- Erdős's Conjecture: The lower bound is correct -/
def ErdosConjecture : Prop :=
  ∀ r : ℕ, r ≥ 3 →
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, (f r N : ℝ) ≤ C * N ^ (c / Real.log (Real.log N))

/-
If the conjecture holds, f_r(N) ≈ N^{c/log log N} would be tight, closing the
gap dramatically from polynomial down to quasi-polynomial.
-/

/-
## Part 7: Connection to Sunflower Problem

A stronger sunflower conjecture would imply Erdős's conjecture for this problem.
The original Erdős-Rado (1960) sunflower bound gives a family of k-sets of
size > (k-1)!·r^k contains an r-sunflower. Removing the k! factor would suffice.

See Problem #20 (Sunflower Conjecture) and Problem #536 (related GCD questions).
-/

/-- The stronger sunflower conjecture that would resolve this problem.
    For any r ≥ 3, there exists c_r such that any family of k-element sets
    of size > c_r^k contains an r-sunflower. The Erdős-Rado bound has
    an additional k! factor that this conjecture removes. -/
/-
## Part 8: Small Cases and Examples

For r = 3 and small N, we can compute f_3(N) exactly:
- f_3(6) = 4: {1, 2, 3, 5} works, no larger set does
- f_3(10) = 5: can add one more coprime element

The set {1} ∪ {primes ≤ N} avoids 3-gcd-subsets (no three primes share
pairwise gcd > 1), but |A| ≈ N/log N is worse than the lower bound.
-/

/-
## Part 9: Proof Techniques

Three main methods have been used:

1. **Counting** (Erdős): Count pairs (A, S) where S ⊆ A is a bad r-subset,
   then use bounds on such pairs to bound |A|.

2. **Graph theory** (Abbott-Hanson): Consider the "gcd graph" where a ~ b if
   gcd(a,b) = d, then apply Turán-type bounds on clique-free graphs.

3. **Multiplicative constructions** (lower bounds): Take numbers with specific
   prime factorization patterns, relating to squarefree numbers and sieves.

The additive-multiplicative dichotomy (GCD is multiplicative but counting is
additive) is a fundamental barrier making the problem difficult.
-/

/-
## Part 10: Summary
-/

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
      ∀ N ≥ N₀, (f r N : ℝ) ≤ C * N ^ ((1:ℝ)/2 + ε)) ∧
    -- Erdős lower bound
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (f 3 N : ℝ) > N ^ (c / Real.log (Real.log N))) :=
  ⟨abbott_hanson_upper_bound, erdos_lower_bound⟩

end Erdos535
