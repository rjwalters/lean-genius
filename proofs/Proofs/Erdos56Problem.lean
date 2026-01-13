/-
Erdős Problem #56: Weakly Divisible Sets

Let N ≥ p_k where p_k is the k-th prime. Suppose A ⊆ {1,...,N} is such that
no k+1 elements of A are pairwise coprime. An example is the set of all
multiples of the first k primes. Is this the largest such set?

**Answer**: NO (disproved) - Ahlswede and Khachatrian (1994)

The original conjecture was disproved for k=212. However, Ahlswede and
Khachatrian later proved (1995) that the conjecture IS true when N is
sufficiently large depending on k.

Reference: https://erdosproblems.com/56
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Order.SupIndep
import Mathlib.Data.Nat.Nth

open scoped Finset

namespace Erdos56

/-!
## Definitions

We formalize the notion of "k-weakly divisible" sets and the key quantities
in Erdős's conjecture.
-/

/--
A set of natural numbers is **k-weakly divisible** if any k+1 elements
of the set are NOT pairwise coprime.

In other words, among any k+1 elements, at least two share a common factor.
This is a natural combinatorial condition arising from the structure of
divisibility among integers.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ s ∈ A.powersetCard (k + 1), ¬Set.Pairwise s Nat.Coprime

/-- The empty set is vacuously k-weakly divisible for any k. -/
lemma weaklyDivisible_empty (k : ℕ) : WeaklyDivisible k ∅ := by
  simp [WeaklyDivisible]

/-- A singleton is k-weakly divisible when k ≥ 1 (no k+1 elements exist). -/
lemma weaklyDivisible_singleton {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    WeaklyDivisible k {n} := by
  simp [WeaklyDivisible, hk]

/-- No non-empty set is 0-weakly divisible (every element is coprime to itself). -/
lemma not_weaklyDivisible_zero {A : Finset ℕ} (h : A.Nonempty) :
    ¬WeaklyDivisible 0 A := by
  simpa [WeaklyDivisible] using ⟨{_}, by simpa using h.choose_spec⟩

/--
**MaxWeaklyDivisible N k** is the maximum cardinality of a k-weakly divisible
subset of {1, 2, ..., N}.

This is the quantity Erdős asked about: how large can such a set be?
-/
noncomputable def MaxWeaklyDivisible (N k : ℕ) : ℕ :=
  sSup {#A | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 1 N) (_ : WeaklyDivisible k A)}

/--
**FirstPrimesMultiples N k** is the set of numbers in {1,...,N} that are
divisible by at least one of the first k primes.

This is Erdős's conjectured optimal set: take all multiples of p₁, p₂, ..., p_k.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

/-!
## The Main Result

Erdős conjectured that FirstPrimesMultiples is always optimal. This was
DISPROVED by Ahlswede and Khachatrian in 1994.
-/

/--
**Erdős Problem #56 (Disproved)**

The conjecture states: for all k > 0 and N ≥ p_{k-1} (the (k-1)-th prime),
the maximum size of a k-weakly divisible subset of {1,...,N} equals
the size of the set of multiples of the first k primes.

This is FALSE. Ahlswede and Khachatrian found a counterexample at k=212.

We state this as an axiom since:
1. The counterexample construction is highly technical
2. It requires careful analysis of specific prime distributions
3. The result has been verified by the mathematical community

Note: The weakened conjecture (for N sufficiently large) IS true.
-/
axiom erdos_56_disproved :
  ¬(∀ k : ℕ, k > 0 →
    ∀ N : ℕ, N ≥ (k - 1).nth Nat.Prime →
    MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card)

/-!
## Verified Examples

We verify some basic cases to build intuition.
-/

/-- For N = 0, the maximum is 0 (empty set). -/
theorem maxWeaklyDivisible_zero : ∀ k : ℕ, MaxWeaklyDivisible 0 k = 0 := by
  intro k
  simp [MaxWeaklyDivisible, Nat.sSup_def]

/-- For k = 0, only the empty set works, so the maximum is 0. -/
theorem maxWeaklyDivisible_k_zero (N : ℕ) : MaxWeaklyDivisible N 0 = 0 := by
  have : ∀ A : Finset ℕ, WeaklyDivisible 0 A ↔ A = ∅ := fun A =>
    ⟨fun h => Finset.not_nonempty_iff_eq_empty.1 (mt not_weaklyDivisible_zero (not_not.2 h)),
     fun h => h ▸ weaklyDivisible_empty _⟩
  simp [this, MaxWeaklyDivisible]

/--
**Intuition**: The set of even numbers {2, 4, 6, ...} is 1-weakly divisible
since any two even numbers share factor 2, so no two are coprime.

More generally, multiples of the first k primes form a k-weakly divisible set.
-/
theorem two_four_not_coprime : ¬Nat.Coprime 2 4 := by native_decide

/-- gcd(2, 4) = 2, demonstrating that even numbers share a common factor. -/
theorem gcd_two_four : Nat.gcd 2 4 = 2 := by native_decide

end Erdos56
