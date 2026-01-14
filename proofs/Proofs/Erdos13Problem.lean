/-
Erdős Problem #13: Divisibility-Free Sets

Let A ⊆ {1,...,N} be such that there are no a,b,c ∈ A with a | (b+c) and
a < min(b,c). Is it true that |A| ≤ N/3 + O(1)?

**Status**: SOLVED (Bedert 2023)

**Answer**: YES. Bedert proved that |A| ≤ N/3 + O(1) holds.

**Lower Bound**: The interval (2N/3, N] ∩ ℕ achieves this bound, showing it's tight.

**Generalization**: For the r-sum version (no a | (b₁ + ... + bᵣ) with a < min(bᵢ)),
Erdős conjectured |A| ≤ N/(r+1) + O(1).

**Prize**: $100

Reference: https://erdosproblems.com/13
Bedert (2023): Solution to the problem
Erdős-Sárközy: Original observation about (2N/3, N]
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos13

/-!
## Background

This problem connects divisibility and additive structure of sets.

A set A ⊆ {1,...,N} is called "divisibility-free" (for our purposes) if there
are no a,b,c ∈ A with:
1. a divides (b + c), AND
2. a < min(b,c)

The second condition is crucial: it says a is strictly smaller than both b and c.
This prevents trivial cases like a = b = c.

The question is: how large can such a set be?
-/

/-!
## Core Definitions
-/

/-- A triple (a,b,c) is "bad" if a | (b+c) and a < min(b,c). -/
def IsBadTriple (a b c : ℕ) : Prop :=
  a ∣ (b + c) ∧ a < b ∧ a < c

/-- A set A is divisibility-free if it contains no bad triples. -/
def DivisibilityFree (A : Finset ℕ) : Prop :=
  ∀ a b c, a ∈ A → b ∈ A → c ∈ A → ¬IsBadTriple a b c

/-- Alternative formulation: for all a,b,c ∈ A with a < min(b,c), a ∤ (b+c). -/
theorem divisibilityFree_iff (A : Finset ℕ) :
    DivisibilityFree A ↔
    ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a < b → a < c → ¬(a ∣ (b + c)) := by
  unfold DivisibilityFree IsBadTriple
  constructor
  · intro h a b c ha hb hc hab hac hdiv
    exact h a b c ha hb hc ⟨hdiv, hab, hac⟩
  · intro h a b c ha hb hc ⟨hdiv, hab, hac⟩
    exact h a b c ha hb hc hab hac hdiv

/-!
## The Upper Third Construction

The interval (2N/3, N] provides a divisibility-free set.
-/

/-- The upper third of {1,...,N}: elements greater than 2N/3. -/
def upperThird (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => 2 * N < 3 * k)

/-- The upper third is divisibility-free.

    Proof: For a,b,c in (2N/3, N] with a < b and a < c:
    - We have b + c > 4N/3
    - We have a < N, so if a | (b+c), then b+c ≥ 2a
    - But b + c ≤ 2N while a > 2N/3, so b+c < 3a
    - Thus b+c = 2a is the only possibility
    - But b,c > 2N/3 and a < min(b,c) implies a > 2N/3 too
    - Then b + c > 4N/3 and 2a > 4N/3, but we also need b + c = 2a
    - With b,c > a > 2N/3, we get b + c > 2a, contradiction. -/
axiom upperThird_divisibilityFree (N : ℕ) : DivisibilityFree (upperThird N)

/-- The size of the upper third is approximately N/3.

    Proof: The upper third contains k with 2N/3 < k ≤ N.
    The smallest such k is ⌊2N/3⌋ + 1, the largest is N.
    So the count is N - ⌊2N/3⌋. -/
axiom upperThird_card (N : ℕ) : (upperThird N).card = N - 2 * N / 3

/-- The upper third achieves the N/3 lower bound. -/
axiom upperThird_achieves_bound (N : ℕ) (hN : N ≥ 3) :
    (upperThird N).card ≥ N / 3

/-!
## Bedert's Theorem (2023)

The main result: |A| ≤ N/3 + O(1) for any divisibility-free A ⊆ {1,...,N}.
-/

/-- Bedert's Theorem (2023): Any divisibility-free subset of {1,...,N} has
    size at most N/3 + O(1).

    The O(1) term is an absolute constant, independent of N. -/
axiom bedert_theorem :
    ∃ C : ℕ, ∀ N : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, a ≤ N ∧ a ≥ 1) →
      DivisibilityFree A →
      A.card ≤ N / 3 + C

/-- Corollary: The upper third construction is essentially optimal.

    Proof: By Bedert's theorem, |A| ≤ N/3 + C. Since |upperThird N| ≥ N/3 - 1,
    we have |A| ≤ |upperThird N| + C + 1. -/
axiom upperThird_optimal :
    ∃ C : ℕ, ∀ N : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, a ≤ N ∧ a ≥ 1) →
      DivisibilityFree A →
      A.card ≤ (upperThird N).card + C

/-!
## The Generalized Problem (r-sums)

Erdős asked about the generalization to r-element sums.
-/

/-- A set has no bad r-tuples if for all a, b₁,...,bᵣ ∈ A with a < min(bᵢ),
    we have a ∤ (b₁ + ... + bᵣ). -/
def RDivisibilityFree (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a : ℕ, a ∈ A →
  ∀ bs : Fin r → ℕ, (∀ i, bs i ∈ A) → (∀ i, a < bs i) →
  ¬(a ∣ ∑ i, bs i)

/-- The case r = 2 recovers the original definition. -/
theorem rDivisibilityFree_two (A : Finset ℕ) :
    RDivisibilityFree 2 A ↔
    ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a < b → a < c → ¬(a ∣ (b + c)) := by
  constructor
  · intro h a b c ha hb hc hab hac
    have h2 := h a ha ![b, c] (by simp [Fin.forall_fin_two, hb, hc])
      (by simp [Fin.forall_fin_two, hab, hac])
    simp [Fin.sum_univ_two] at h2
    exact h2
  · intro h a ha bs hbs hlt hdiv
    have := h a (bs 0) (bs 1) ha (hbs 0) (hbs 1) (hlt 0) (hlt 1)
    simp [Fin.sum_univ_two] at hdiv
    exact this hdiv

/-- The upper (r/(r+1)) fraction should be r-divisibility-free.

    For r = 2: upper 2/3 works (our upperThird)
    For r = 3: upper 3/4 should work
    etc. -/
def upperFraction (r N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun k => r * N < (r + 1) * k)

/-- Erdős's Conjecture for r-sums: |A| ≤ N/(r+1) + O(1). -/
def ErdosRSumConjecture (r : ℕ) : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, ∀ A : Finset ℕ,
    (∀ a ∈ A, a ≤ N ∧ a ≥ 1) →
    RDivisibilityFree r A →
    A.card ≤ N / (r + 1) + C

/-- The r = 2 case is Bedert's theorem. -/
theorem erdos_rsum_two : ErdosRSumConjecture 2 := by
  obtain ⟨C, hC⟩ := bedert_theorem
  use C
  intro N A hA hfree
  apply hC N A hA
  rw [divisibilityFree_iff]
  rw [rDivisibilityFree_two] at hfree
  exact hfree

/-!
## Why the Bound is N/3

Intuition for why N/3 is the right answer:

Consider the residues mod 3. If A contains elements from all three residue
classes, we can often find a bad triple. The construction (2N/3, N] essentially
uses only one residue class worth of elements.

More precisely: if a, b, c have a < b, a < c and a | (b+c), then
b + c ≥ 2a (since b,c > a and b + c is a multiple of a ≥ 2a).
In the upper third, b + c > 4N/3 but 2a < 2N, which limits possibilities.
-/

/-- Elements in the upper third satisfy 2N/3 < k ≤ N. -/
theorem mem_upperThird_iff (N k : ℕ) :
    k ∈ upperThird N ↔ k ≤ N ∧ 2 * N < 3 * k := by
  unfold upperThird
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨hk, h2⟩
    exact ⟨by omega, h2⟩
  · intro ⟨hk, h2⟩
    exact ⟨by omega, h2⟩

/-!
## Connection to Sum-Free Sets

This problem is related to (but distinct from) sum-free sets.

A set is sum-free if a + b ≠ c for all a,b,c in the set.
Here, we allow a + b = c but forbid divisibility relationships.

The upper third (2N/3, N] is also a classic example of a sum-free set!
For a,b,c in (2N/3, N], we have a + b > 4N/3 > N ≥ c.
-/

/-- The upper third is also sum-free. -/
def SumFree (A : Finset ℕ) : Prop :=
  ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a + b ≠ c

/-- The upper third is sum-free.

    Proof: For a,b,c in (2N/3, N], we have a + b > 4N/3 > N ≥ c,
    so a + b > c, hence a + b ≠ c. -/
axiom upperThird_sumFree (N : ℕ) (hN : N ≥ 1) : SumFree (upperThird N)

/-!
## Summary

**Problem Status: SOLVED**

Erdős Problem 13 asked whether divisibility-free sets A ⊆ {1,...,N}
(no a,b,c with a | (b+c) and a < min(b,c)) have |A| ≤ N/3 + O(1).

**Resolution**: Bedert (2023) proved the affirmative answer, earning the $100 prize.

**Key insight**: The upper third (2N/3, N] is both:
- Divisibility-free (the condition cannot be satisfied)
- Sum-free (a + b > c for all elements)
- Optimal up to O(1) (achieves the N/3 bound)

**Open**: The generalized r-sum conjecture |A| ≤ N/(r+1) + O(1) for r ≥ 3.

References:
- Bedert (2023): Solution to the problem
- Erdős-Sárközy: Original construction and observations
- Related to Problems #12 (infinite version) and #131
-/

end Erdos13
