/-
# Erdős Problem #882 — OQ-03-OQ-01: A valid set is an antichain, and no element divides its total

Erdős Problem #882 asks for the largest `A ⊆ {1,…,n}` whose non-empty subset
sums are pairwise non-dividing (answer: `(1+o(1)) log₂ n`).  The sibling file
`Erdos882ProblemOQ03` establishes that the predicate `ValidSubset` is *downward
closed* (any subset of a valid set is valid).  That file works "downward" along
the subset lattice; this one works in the orthogonal direction, extracting
structure of `A` itself from the constraint on its subset sums.

The pivot is the singleton embedding `A ⊆ subsetSums A`: every element `a ∈ A`
appears verbatim as the subset sum of `{a}`.  Two structural consequences fall
out, both fully machine-checked (0 axioms, 0 sorries):

  * `validSubset_antichain`        — **a valid set is itself divisibility-free**:
    the hypothesis only constrains *subset sums*, yet it forces the underlying
    set `A` to be an antichain under divisibility (its elements pairwise do not
    divide one another).
  * `validSubset_elem_not_dvd_sum` — **no element of a valid set divides the
    grand total** `∑ A` (whenever `A` has at least two elements): the element is
    a singleton subset sum, the total is the full subset sum, the two are
    distinct (the element is strictly smaller, since the others are positive),
    so the divisibility-free condition applies.

Both are genuine constraints the optimization problem imposes "for free" on its
admissible sets, complementing the downward-closure monotonicity used by the
upper-bound argument.

Self-contained: the four predicates are re-declared here using the modern
Finset API (the original parent file predates the current Mathlib toolchain and
no longer builds), so this contribution stands on its own.

Reference: Erdős Problem #882, https://erdosproblems.com/882
-/

import Mathlib

namespace Erdos882OQ03OQ01

open Finset BigOperators

/-- All non-empty subsets of a finite set. -/
def nonemptySubsets (A : Finset ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter (· ≠ ∅)

/-- The set of all non-empty subset sums `{∑_{a ∈ S} a : ∅ ≠ S ⊆ A}`. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsets A).image (fun S => S.sum id)

/-- No two distinct elements of a set divide each other. -/
def DivisibilityFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬(a ∣ b) ∧ ¬(b ∣ a)

/-- `A` is a valid subset of `{1,…,n}` with divisibility-free subset sums. -/
def ValidSubset (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧ DivisibilityFree (subsetSums A)

/-- Every element of `A` is a subset sum of `A`: it is the sum of the
    singleton `{a}`. -/
theorem self_mem_subsetSums {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∈ subsetSums A := by
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨{a}, ?_, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.singleton_subset_iff.mpr ha, Finset.singleton_ne_empty a⟩

/-- The singleton embedding `A ⊆ subsetSums A`. -/
theorem subset_subsetSums (A : Finset ℕ) : A ⊆ subsetSums A :=
  fun _ ha => self_mem_subsetSums ha

/-- The total sum `∑ A` is a subset sum of any non-empty `A` (the sum of the
    full set `A` itself). -/
theorem total_mem_subsetSums {A : Finset ℕ} (hA : A.Nonempty) :
    A.sum id ∈ subsetSums A := by
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨A, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.Subset.refl A, Finset.nonempty_iff_ne_empty.mp hA⟩

/-- **A valid set is itself divisibility-free.**  The hypothesis only constrains
    the *subset sums*, but since each element appears as a singleton subset sum,
    divisibility-freeness of `subsetSums A` restricts to `A`.  In particular the
    elements of an extremal admissible set already form an antichain under
    divisibility. -/
theorem validSubset_antichain {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A) :
    DivisibilityFree A :=
  fun a ha b hb hab =>
    hA.2 a (self_mem_subsetSums ha) b (self_mem_subsetSums hb) hab

/-- Direct corollary: distinct elements of a valid set never divide one
    another. -/
theorem validSubset_not_dvd {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) : ¬(a ∣ b) :=
  (validSubset_antichain hA a ha b hb hab).1

/-- In a valid set with at least two elements, every element is strictly smaller
    than the grand total `∑ A`: the remaining elements are positive, so they
    contribute a positive amount on top of `a`. -/
theorem elem_lt_sum {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    (hcard : 1 < A.card) {a : ℕ} (ha : a ∈ A) : a < A.sum id := by
  -- pick a second element `b ≠ a`
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
  have hbpos : 1 ≤ b := (hA.1 b hb).1
  have hb_erase : b ∈ A.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
  -- the others sum to at least `b ≥ 1`
  have herase : 1 ≤ (A.erase a).sum id :=
    le_trans hbpos (Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hb_erase)
  -- `∑ A = a + ∑ (A \ {a})`
  have hsplit : id a + (A.erase a).sum id = A.sum id := Finset.add_sum_erase A id ha
  rw [id_eq] at hsplit
  rw [← hsplit]
  omega

/-- **No element of a valid set divides the grand total.**  For a valid set with
    at least two elements, an element `a` is a singleton subset sum and the total
    `∑ A` is the full subset sum; since `a < ∑ A` they are distinct, so the
    divisibility-free condition forbids `a ∣ ∑ A`. -/
theorem validSubset_elem_not_dvd_sum {n : ℕ} {A : Finset ℕ}
    (hA : ValidSubset n A) (hcard : 1 < A.card) {a : ℕ} (ha : a ∈ A) :
    ¬(a ∣ A.sum id) := by
  have hne : a ≠ A.sum id := ne_of_lt (elem_lt_sum hA hcard ha)
  have hAne : A.Nonempty := ⟨a, ha⟩
  exact (hA.2 a (self_mem_subsetSums ha) (A.sum id)
    (total_mem_subsetSums hAne) hne).1

end Erdos882OQ03OQ01
