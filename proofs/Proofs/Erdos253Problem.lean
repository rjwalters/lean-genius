/-
Erdős Problem #253: Subset Sums and Arithmetic Progressions

**Conjecture (Erdős, 1961)**: Let $a_1 < a_2 < \cdots$ be an infinite sequence
of positive integers such that $a_{i+1}/a_i \to 1$. If every arithmetic
progression contains infinitely many integers which are sums of distinct $a_i$,
then every sufficiently large integer is a sum of distinct $a_i$.

**Answer**: FALSE - disproved by Cassels (1960)

Cassels constructed a counterexample: a sequence satisfying all hypotheses
where the set of subset sums is NOT cofinite (i.e., infinitely many integers
are not representable as subset sums).

Reference: https://erdosproblems.com/253
-/

import Mathlib

open Set Filter Topology

namespace Erdos253

/-! ## Definitions -/

/-- The set of all finite subset sums of a set S.
    An element is a subset sum if it equals the sum of some finite subset of S. -/
def subsetSums (S : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ (F : Finset ℕ), ↑F ⊆ S ∧ F.sum id = n}

/-- A set is an infinite arithmetic progression with common difference d > 0
    if it has the form {a, a+d, a+2d, ...} for some starting value a. -/
def IsInfiniteAP (L : Set ℕ) : Prop :=
  ∃ (a d : ℕ), d > 0 ∧ L = {n : ℕ | ∃ k : ℕ, n = a + k * d}

/-- A sequence a : ℕ → ℕ has the "AP representation property" if:
    1. It is strictly increasing
    2. Every infinite arithmetic progression contains infinitely many
       integers that are sums of distinct terms from the sequence -/
def HasAPRepresentationProperty (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧
  ∀ L : Set ℕ, IsInfiniteAP L → (subsetSums (range a) ∩ L).Infinite

/-- A sequence has "ratio tending to 1" if a_{n+1}/a_n → 1 as n → ∞ -/
def HasRatioTendingToOne (a : ℕ → ℕ) : Prop :=
  Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (nhds 1)

/-! ## Main Result -/

/--
**Erdős Problem #253** (Disproved):

The conjecture states: If a strictly increasing sequence (aₙ) with aₙ₊₁/aₙ → 1
has the property that every arithmetic progression contains infinitely many
subset sums, then all sufficiently large integers are subset sums.

This is FALSE. Cassels (1960) constructed a counterexample: a sequence
satisfying all the hypotheses but where infinitely many integers cannot
be represented as sums of distinct terms.

We state the negation as an axiom, since Cassels' construction is intricate
and involves detailed analysis of the sequence's growth rate and representation
properties.
-/
axiom erdos_253_disproved :
  ¬∀ (a : ℕ → ℕ),
    (∀ n, 0 < a n) →
    HasAPRepresentationProperty a →
    HasRatioTendingToOne a →
    (subsetSums (range a))ᶜ.Finite

/-! ## Supporting Results -/

/-- The empty set is always a subset sum (gives 0) -/
theorem zero_mem_subsetSums (S : Set ℕ) : 0 ∈ subsetSums S := by
  use ∅
  constructor
  · simp
  · simp

/-- Any element of S is a subset sum (singleton sum) -/
theorem mem_subsetSums_of_mem {S : Set ℕ} {x : ℕ} (hx : x ∈ S) :
    x ∈ subsetSums S := by
  use {x}
  constructor
  · simpa using hx
  · simp

/-- The natural numbers form an infinite arithmetic progression (d = 1) -/
theorem nat_is_infinite_AP : IsInfiniteAP (univ : Set ℕ) := by
  use 0, 1
  constructor
  · norm_num
  · ext n
    simp only [mem_univ, true_iff, mem_setOf_eq]
    use n
    omega

/-- Example: {0, 2, 4, 6, ...} is an infinite AP -/
theorem evens_is_infinite_AP : IsInfiniteAP {n : ℕ | Even n} := by
  use 0, 2
  constructor
  · norm_num
  · ext n
    simp only [mem_setOf_eq]
    constructor
    · intro ⟨k, hk⟩
      use k
      omega
    · intro ⟨k, hk⟩
      use k
      omega

end Erdos253
