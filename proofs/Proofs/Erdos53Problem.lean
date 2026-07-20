/-
# Erdős Problem 53: Sums and Products of Distinct Elements

*Reference:* [erdosproblems.com/53](https://www.erdosproblems.com/53)

Let `A` be a finite set of integers. Is it true that for every `k`, if `|A|`
is sufficiently large (depending on `k`), then there are at least `|A|^k`
integers representable as sums or products of distinct elements of `A`?

This problem was posed by Erdős and Szemerédi (1983) and resolved affirmatively
by Chang (2003). Erdős and Szemerédi also proved an upper bound:
there exist arbitrarily large sets `A` where the count of representable
integers is at most `exp(c · (log |A|)² · log log |A|)`.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-
## Section 1: Subset sums and products

We define the set of integers representable as a sum of distinct elements
of a finite set, and similarly for products.
-/

namespace Erdos53

open Finset

/-- The set of all sums of distinct elements (subsets) of a finite integer set. -/
def subsetSums (A : Finset ℤ) : Finset ℤ :=
  (A.powerset).image (fun S => S.sum id)

/-- The set of all products of distinct elements (nonempty subsets) of a finite integer set. -/
def subsetProducts (A : Finset ℤ) : Finset ℤ :=
  (A.powerset.filter (fun S => S.Nonempty)).image (fun S => S.prod id)

/-- The set of integers representable as either a sum or product of distinct elements. -/
def sumsOrProducts (A : Finset ℤ) : Finset ℤ :=
  subsetSums A ∪ subsetProducts A

/-
## Section 2: The Erdős–Szemerédi conjecture (Problem 53)

For every `k`, if `|A|` is large enough, then `|sumsOrProducts A| ≥ |A|^k`.
-/

/-- Erdős Problem 53: For every k, there exists N₀ such that for any finite
    set A of integers with |A| ≥ N₀, the number of integers representable
    as sums or products of distinct elements of A is at least |A|^k. -/
def ErdosProblem53 : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
      (sumsOrProducts A).card ≥ A.card ^ k

/-
## Section 3: Chang's theorem (2003)

Chang proved the conjecture affirmatively, resolving Problem 53.
-/

/-  Chang's theorem (2003): Erdős Problem 53 holds. -/
/-
## Section 4: The Erdős–Szemerédi upper bound

Erdős and Szemerédi showed that arbitrarily large sets exist where the count
of representable integers is bounded by `exp(c · (log |A|)² · log log |A|)`.
This shows the growth cannot be *too* fast.
-/

/-  There exists a constant c > 0 and arbitrarily large sets A where the
    number of representable integers is at most exp(c · (log |A|)² · log log |A|). -/
/-
## Section 5: Sum-product phenomena connection

This problem is closely related to the Erdős–Szemerédi sum-product conjecture
(Problem 52), which concerns `|A + A| + |A · A|` for a single set `A`.
The distinction is that Problem 53 asks about sums and products of *distinct*
elements (subsets), while Problem 52 concerns pairwise sums and products.
-/

/-- The sumset A + A. -/
def sumset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The product set A · A. -/
def productset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 * p.2)

/-- The sum-product conjecture (Problem 52) asserts that for every ε > 0,
    |A+A| + |A·A| ≥ |A|^{2-ε} for large enough |A|.
    This is a related but distinct problem. -/
def SumProductConjecture : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
      (sumset A).card + (productset A).card ≥ A.card ^ 2 / (A.card * εNum / εDen + 1)

/-
## Section 6: Counting distinct-element representations

We can count how many integers have a representation as a sum of distinct
elements versus a product of distinct elements.
-/

/-- Count of integers representable as subset sums. -/
def subsetSumCount (A : Finset ℤ) : ℕ := (subsetSums A).card

/-- Count of integers representable as subset products. -/
def subsetProductCount (A : Finset ℤ) : ℕ := (subsetProducts A).card

/-
## Section 7: Foundational lemmas (axiom-free)

The Erdős–Szemerédi conjecture (Chang's theorem) and the upper bound require deep
additive combinatorics beyond current Mathlib and stay documented above only.  The
elementary structural facts about the set-valued definitions in this file are,
however, fully machine-checkable.  All lemmas below are axiom-free
(`propext / Classical.choice / Quot.sound` only). -/

/-- The empty sum (empty subset) shows `0` is always a subset sum. -/
theorem zero_mem_subsetSums (A : Finset ℤ) : (0 : ℤ) ∈ subsetSums A := by
  rw [subsetSums, Finset.mem_image]
  exact ⟨∅, Finset.empty_mem_powerset A, by simp⟩

/-- Every element of `A` is itself a subset sum (via the singleton subset). -/
theorem mem_subsetSums_of_mem {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    a ∈ subsetSums A := by
  rw [subsetSums, Finset.mem_image]
  exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha), by simp⟩

/-- Every element of `A` is itself a subset product (via the singleton subset). -/
theorem mem_subsetProducts_of_mem {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    a ∈ subsetProducts A := by
  rw [subsetProducts, Finset.mem_image]
  refine ⟨{a}, ?_, by simp⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
    Finset.singleton_nonempty a⟩

/-- Subset sums are among the sum-or-product representable integers. -/
theorem subsetSums_subset_sumsOrProducts (A : Finset ℤ) :
    subsetSums A ⊆ sumsOrProducts A := by
  rw [sumsOrProducts]; exact Finset.subset_union_left

/-- Subset products are among the sum-or-product representable integers. -/
theorem subsetProducts_subset_sumsOrProducts (A : Finset ℤ) :
    subsetProducts A ⊆ sumsOrProducts A := by
  rw [sumsOrProducts]; exact Finset.subset_union_right

/-- There are at most `2^{|A|}` subset sums (image of the powerset). -/
theorem subsetSums_card_le (A : Finset ℤ) : (subsetSums A).card ≤ 2 ^ A.card := by
  rw [subsetSums]
  calc (A.powerset.image (fun S => S.sum id)).card
      ≤ A.powerset.card := Finset.card_image_le
    _ = 2 ^ A.card := Finset.card_powerset A

/-- Subset sums are monotone in the ground set. -/
theorem subsetSums_mono {A B : Finset ℤ} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B := by
  rw [subsetSums, subsetSums]
  exact Finset.image_subset_image (Finset.powerset_mono.mpr h)

/-- The union count dominates the subset-sum count. -/
theorem subsetSumCount_le_card (A : Finset ℤ) :
    subsetSumCount A ≤ (sumsOrProducts A).card := by
  rw [subsetSumCount]
  exact Finset.card_le_card (subsetSums_subset_sumsOrProducts A)

/-- The union count dominates the subset-product count. -/
theorem subsetProductCount_le_card (A : Finset ℤ) :
    subsetProductCount A ≤ (sumsOrProducts A).card := by
  rw [subsetProductCount]
  exact Finset.card_le_card (subsetProducts_subset_sumsOrProducts A)

/-- The sumset `A + A` has at most `|A|²` elements. -/
theorem sumset_card_le (A : Finset ℤ) : (sumset A).card ≤ A.card ^ 2 := by
  rw [sumset]
  calc ((A ×ˢ A).image (fun p => p.1 + p.2)).card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product A A
    _ = A.card ^ 2 := (sq _).symm

/-- The product set `A · A` has at most `|A|²` elements. -/
theorem productset_card_le (A : Finset ℤ) : (productset A).card ≤ A.card ^ 2 := by
  rw [productset]
  calc ((A ×ˢ A).image (fun p => p.1 * p.2)).card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product A A
    _ = A.card ^ 2 := (sq _).symm

/-- The empty set has exactly one subset sum, namely `0`. -/
theorem subsetSums_empty : subsetSums (∅ : Finset ℤ) = {0} := by
  rw [subsetSums, Finset.powerset_empty, Finset.image_singleton, Finset.sum_empty]

end Erdos53
