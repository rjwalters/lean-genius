/-
Erdős Problem #326: Additive Bases and Non-Convergent Subsequences

Let A ⊂ ℕ be an additive basis of order 2 (every sufficiently large natural
number can be written as a sum of two elements of A). Must there exist a
subset B ⊆ A which is also a basis such that lim(k→∞) bₖ/k² does not exist?

**Status**: OPEN

Erdős originally asked whether this was true with A = B, but Cassels (1957)
disproved that version by constructing a basis A where aₖ/k² converges.

Reference: https://erdosproblems.com/326
-/

import Mathlib

open Filter Set
open scoped Topology

namespace Erdos326

/-!
## Additive Bases

An additive basis of order k is a set A ⊆ ℕ such that every sufficiently large
natural number can be written as a sum of at most k elements of A (with repetition).

The classic example of an order 2 basis is the perfect squares:
Lagrange's theorem states every natural number is a sum of four squares.
-/

/--
A set A ⊆ ℕ is an additive basis if every sufficiently large natural number
can be written as a sum of elements from A.
-/
def IsAddBasis (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ (k : ℕ) (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ (∑ i, f i) = n

/--
A set A ⊆ ℕ is an additive basis of order k if every sufficiently large natural
number can be written as a sum of at most k elements from A.
-/
def IsAddBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ (m : ℕ) (_ : m ≤ k) (f : Fin m → ℕ),
    (∀ i, f i ∈ A) ∧ (∑ i, f i) = n

/-- An order k basis is an additive basis -/
theorem IsAddBasisOfOrder.isAddBasis {A : Set ℕ} {k : ℕ} (h : IsAddBasisOfOrder A k) :
    IsAddBasis A := by
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  obtain ⟨m, _, f, hf, hsum⟩ := hN n hn
  exact ⟨m, f, hf, hsum⟩

/-!
## The Growth Rate Question

For a basis B = {b₁ < b₂ < ···}, the sequence bₖ/k² measures how "sparse" the
basis is. A classic result shows that any order 2 basis must satisfy
bₖ ≤ Ck² for some constant C (it can't grow faster than quadratically).

The question is about the limit behavior: must every subset basis have a
non-convergent ratio bₖ/k²?
-/

/--
Given an increasing enumeration b : ℕ → ℕ of elements of a set,
this function computes bₖ/k² (using real division).
-/
noncomputable def growthRatio (b : ℕ → ℕ) (k : ℕ) : ℝ :=
  (b k : ℝ) / (k : ℝ) ^ 2

/--
The sequence bₖ/k² converges to x if the growth ratio tends to x.
-/
def HasGrowthLimit (b : ℕ → ℕ) (x : ℝ) : Prop :=
  Tendsto (growthRatio b) atTop (𝓝 x)

/--
The sequence bₖ/k² has no limit if it doesn't converge to any real number.
-/
def HasNoGrowthLimit (b : ℕ → ℕ) : Prop :=
  ∀ x : ℝ, ¬ HasGrowthLimit b x

/-!
## Main Theorem (OPEN)

Erdős Problem #326: Let A be an additive basis of order 2. Must there exist
a subset B ⊆ A which is also a basis, enumerated as B = {b₁ < b₂ < ···},
such that lim(k→∞) bₖ/k² does not exist?

This remains open. We state it with an unknown answer placeholder.
-/

/--
**Erdős Problem #326 (OPEN)**:

Given any additive basis A of order 2, does there always exist a subset
B ⊆ A which is also an additive basis, with increasing enumeration b,
such that the growth ratio bₖ/k² has no limit?

The answer is currently unknown.
-/
axiom erdos_326_statement :
    (∀ (A : Set ℕ), IsAddBasisOfOrder A 2 →
      ∃ (b : ℕ → ℕ), StrictMono b ∧ (∀ n, b n ∈ A) ∧
        IsAddBasis (range b) ∧ HasNoGrowthLimit b) ∨
    ¬(∀ (A : Set ℕ), IsAddBasisOfOrder A 2 →
      ∃ (b : ℕ → ℕ), StrictMono b ∧ (∀ n, b n ∈ A) ∧
        IsAddBasis (range b) ∧ HasNoGrowthLimit b)

/-!
## Cassels' Result (1957)

Erdős originally asked whether every basis A (with A = B) has the property
that aₖ/k² diverges. Cassels disproved this by showing there exists a basis
where the growth ratio converges.
-/

/--
**Cassels' Theorem (1957)**:

There exists an additive basis A of order 2, enumerated as A = {a₁ < a₂ < ···},
and a positive real x, such that lim(k→∞) aₖ/k² = x.

This disproves Erdős's original formulation where A = B was required.
-/
axiom cassels_1957 :
    ∃ (a : ℕ → ℕ) (_ : StrictMono a) (_ : IsAddBasisOfOrder (range a) 2)
      (x : ℝ) (_ : 0 < x), HasGrowthLimit a x

/-!
## Key Observations

1. Any order 2 basis must have density at least O(√n) - there must be at least
   C√n elements up to n, which means the k-th element is at most O(k²).

2. Cassels' construction is delicate: he builds a basis that grows exactly
   like ck² for some constant c.

3. The open question asks whether, given ANY order 2 basis A, we can find
   a sub-basis B that oscillates in its growth rate.
-/

/--
For any order 2 basis, elements can't grow faster than k².
This is a standard result from additive combinatorics.
-/
axiom basis_upper_bound :
    ∀ (a : ℕ → ℕ), StrictMono a → IsAddBasisOfOrder (range a) 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, (a k : ℝ) ≤ C * (k : ℝ) ^ 2

end Erdos326
