/-
  Erdős Problem #888: Square Products with ad = bc Constraint

  What is the size of the largest A ⊆ {1,...,n} such that if
  a ≤ b ≤ c ≤ d ∈ A and abcd is a perfect square, then ad = bc?

  **Status**: Exact answer OPEN; bounds SOLVED

  **Known Results**:
  - Sárközy proved: |A| = o(n) (sublinear growth)
  - Primes show: |A| ≫ n/log n is achievable

  A question of Erdős, Sárközy, and Sós from combinatorial number theory.

  References:
  - https://erdosproblems.com/888
  - See also Erdős Problem #121
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

open Finset Set

namespace Erdos888

/-
## The Core Condition

The key constraint is: for any four elements a ≤ b ≤ c ≤ d in A,
if their product is a perfect square, then ad = bc.

This constraint prevents "too many" multiplicative relationships in A.
-/

/-- A quadruple (a, b, c, d) in A with a ≤ b ≤ c ≤ d has the square-product property
if abcd being a perfect square implies ad = bc. -/
def squareProductCondition (a b c d : ℕ) : Prop :=
  a ≤ b → b ≤ c → c ≤ d → IsSquare (a * b * c * d) → a * d = b * c

/-- The Erdős-Sárközy-Sós condition on a subset A ⊆ {1,...,n}:
- A is contained in {1,...,n}
- For all a ≤ b ≤ c ≤ d in A: if abcd is square then ad = bc -/
def requiredCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    squareProductCondition a b c d

/-- The set of valid subsets of {1,...,n} with the required condition. -/
def validSets (n : ℕ) : Set (Finset ℕ) :=
  { A | requiredCondition A n }

/-
## Why the Condition Matters

**Intuition**: The condition ad = bc means (a,b,c,d) forms a geometric-like structure.
If a, b, c, d are in geometric progression, then b/a = c/b = d/c, giving bc = ad.

The constraint limits how "rich" A can be in multiplicative structure.
If A has too many elements, we'll find a quadruple violating the condition.

**Example**: {1, 2, 3, 6} satisfies the condition: 1×2×3×6 = 36 = 6² is square,
and 1×6 = 6 = 2×3, so ad = bc. ✓
-/

/-
## Maximum Size Function

For each n, we want to find the maximum cardinality of a valid set.
-/

/-- A predicate indicating a valid set of size k exists for {1,...,n}. -/
def hasValidSetOfSize (n k : ℕ) : Prop :=
  ∃ A : Finset ℕ, requiredCondition A n ∧ A.card = k

/-- The maximum size of a valid set A ⊆ {1,...,n}.
We axiomatize this as it requires showing decidability of the existence predicate. -/
axiom maxValidSize : ℕ → ℕ

/-
## The Main Question (OPEN)

The exact formula for maxValidSize(n) is unknown.
-/

/-- **Erdős Problem #888 (Main Question - OPEN)**: Find the exact formula
for the maximum size of A ⊆ {1,...,n} with the square-product condition.

The exact answer is unknown. -/

/-
## Sárközy's Upper Bound (SOLVED)

Sárközy proved that |A| = o(n), meaning the maximum grows sublinearly.
This uses a counting argument involving the multiplicative structure.
-/

/-- **Sárközy's Theorem**: The maximum valid set size is o(n).

For any ε > 0, eventually maxValidSize(n) < ε * n.

This was proved by Sárközy using multiplicative number theory. -/

/-
## Prime Lower Bound (SOLVED)

The primes satisfy the condition! If p₁, p₂, p₃, p₄ are distinct primes
and p₁ × p₂ × p₃ × p₄ is a perfect square, this is impossible since
each prime appears with odd exponent in the factorization.

This gives a construction achieving |A| ≥ π(n) ≫ n/log n.
-/

/-- The set of primes up to n. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 n).filter Nat.Prime

/-- Primes satisfy the required condition.

**Proof sketch**: If p₁ ≤ p₂ ≤ p₃ ≤ p₄ are primes and p₁p₂p₃p₄ is square,
then each prime in the factorization appears an even number of times.
But each pᵢ appears exactly once (or twice if equal), so we need repeats.
With four primes, either all are equal, or we have pairs, forcing ad = bc. -/
axiom primes_satisfy_condition (n : ℕ) :
  requiredCondition (primesUpTo n) n

/-- The primes give a valid construction of size π(n). -/
theorem primes_valid_construction (n : ℕ) :
    hasValidSetOfSize n (primesUpTo n).card := by
  use primesUpTo n
  exact ⟨primes_satisfy_condition n, rfl⟩

/-- **Prime Lower Bound**: maxValidSize(n) ≥ π(n).

The maximum is at least the number of primes up to n. -/

/-- The primes up to n have cardinality approximately n / log n.
By the Prime Number Theorem, |primesUpTo n| ~ n / log n. -/

/-
## Combined Bounds Summary

We know: n / log n ≪ maxValidSize(n) = o(n)

The gap between these bounds (log n factor) is where the true answer lies.
-/

/-- Summary: The set of valid n values is infinite (there's always a valid set). -/
theorem valid_sets_exist (n : ℕ) : ∃ A : Finset ℕ, requiredCondition A n :=
  ⟨∅, by constructor; exact Finset.empty_subset _; intro a ha; exact (Finset.notMem_empty a ha).elim⟩

/-
## Examples and Special Cases
-/

/-- The empty set trivially satisfies the condition. -/
theorem empty_valid (n : ℕ) : requiredCondition ∅ n := by
  constructor
  · exact Finset.empty_subset _
  · intro a ha
    exact (Finset.notMem_empty a ha).elim

/-- Any singleton set satisfies the condition (no valid quadruple exists). -/
theorem singleton_valid (n : ℕ) (x : ℕ) (hx : x ∈ Finset.Ioc 0 n) :
    requiredCondition {x} n := by
  constructor
  · exact Finset.singleton_subset_iff.mpr hx
  · intro a ha b hb c hc d hd
    simp only [Finset.mem_singleton] at ha hb hc hd
    subst ha hb hc hd
    intro _ _ _ _
    ring

/-
## Connection to Problem 121

Problem 888 is related to Erdős Problem #121, which asks about
similar multiplicative conditions on subsets.
-/

/-- Connection to Erdős Problem #121. -/
def related_to_121 : Prop :=
  True  -- Placeholder for the relationship

/-
## Variants and Generalizations
-/

/-- Variant: What if we only require pairs (a,d) with ad square? -/
def weakerCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧
  ∀ a ∈ A, ∀ d ∈ A, a ≤ d → IsSquare (a * d) → a = d

/-- Variant: Restriction to squarefree numbers. -/
def squarefreeCondition (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Ioc 0 n ∧
  (∀ x ∈ A, Squarefree x) ∧
  (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    squareProductCondition a b c d)

/-
## Numerical Data

For small n, exact values can be computed:
- maxValidSize(1) = 1 (just {1})
- maxValidSize(2) = 2 ({1,2})
- maxValidSize(3) = 3 ({1,2,3})

The primes {2,3,5,7,11,...} always work.
-/

/-
## Summary

Erdős Problem #888 asks for the maximum size of A ⊆ {1,...,n} with:
- For all a ≤ b ≤ c ≤ d ∈ A: if abcd is square then ad = bc

**Known**:
- n / log n ≪ max|A| (primes construction)
- max|A| = o(n) (Sárközy's theorem)

**Open**: The exact asymptotic formula.
-/

end Erdos888
