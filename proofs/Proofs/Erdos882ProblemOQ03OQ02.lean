/-
# Erdős Problem #882 — OQ-03-OQ-02: Subset sums strictly increase along inclusion and no proper subset sum divides the total

Erdős Problem #882 asks for the largest `A ⊆ {1,…,n}` whose non-empty subset
sums are pairwise non-dividing (answer: `(1+o(1)) log₂ n`).  Two earlier files in
this lineage extract structure of a feasible set `A`:

  * `Erdos882ProblemOQ03`     — `ValidSubset` is *downward closed* (subset-lattice
    direction): any subset of a valid set is valid.
  * `Erdos882ProblemOQ03OQ01` — a valid set is itself an *antichain under
    divisibility*, and (for `|A| ≥ 2`) no single *element* divides the grand
    total `∑ A`.

This file works the **chain** direction of the subset lattice.  The summing map
`S ↦ ∑ S` is strictly monotone along strict inclusions (the extra elements are
positive), so any two subset sums coming from a strictly nested pair `S ⊊ T` are
distinct.  Combined with the divisibility-free hypothesis this yields the
headline:

  * `subsetSum_not_dvd_of_ssubset` — for a valid `A` and a strict chain
    `∅ ≠ S ⊊ T ⊆ A`, neither subset sum divides the other.
  * `proper_subset_not_dvd_total`  — **no proper non-empty subset sum divides the
    total** `∑ A`.  Taking `S = {a}` recovers the sibling's
    `validSubset_elem_not_dvd_sum` (here `elem_not_dvd_total`), so the per-element
    statement is just the singleton case of a uniform chain phenomenon.

Geometrically: along every chain in the subset lattice of a feasible set the
sums form a *strictly increasing* sequence that is *pairwise non-dividing* — a
strict chain in value that is simultaneously an antichain in divisibility.

Self-contained: the four predicates are re-declared here using the modern Finset
API (the original parent `Erdos882Problem.lean` predates the current Mathlib
toolchain and no longer builds), so this contribution stands on its own.

Reference: Erdős Problem #882, https://erdosproblems.com/882
-/

import Mathlib

namespace Erdos882OQ03OQ02

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

/-- Every non-empty subset `S ⊆ A` contributes its sum `∑ S` to `subsetSums A`.
    This is the general membership statement; the singleton case `a = ∑ {a}` and
    the full case `∑ A` are the two extremes used by the sibling file. -/
theorem subsetSum_mem {A S : Finset ℕ} (hSA : S ⊆ A) (hS : S.Nonempty) :
    S.sum id ∈ subsetSums A := by
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨S, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hSA, Finset.nonempty_iff_ne_empty.mp hS⟩

/-- **Strict monotonicity of the summing map along inclusions.**  If `S ⊊ T ⊆ A`
    then `∑ S < ∑ T`: the elements of `T` (hence of `A`) are positive, so the
    witnessing element of `T ∖ S` contributes a strictly positive amount. -/
theorem subsetSum_lt_of_ssubset {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    {S T : Finset ℕ} (hST : S ⊂ T) (hTA : T ⊆ A) :
    S.sum id < T.sum id := by
  obtain ⟨i, hiT, hiS⟩ := Finset.exists_of_ssubset hST
  have hipos : 0 < id i := by
    have hi1 : 1 ≤ i := (hA.1 i (hTA hiT)).1
    simpa using hi1
  exact Finset.sum_lt_sum_of_subset hST.subset hiT hiS hipos
    (fun j _ _ => Nat.zero_le _)

/-- Every proper non-empty subset sum is strictly below the total `∑ A`. -/
theorem subsetSum_lt_total {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    {S : Finset ℕ} (hSA : S ⊂ A) :
    S.sum id < A.sum id :=
  subsetSum_lt_of_ssubset hA hSA (Finset.Subset.refl A)

/-- **Along a strict chain neither subset sum divides the other.**  For a valid
    `A` and `∅ ≠ S ⊊ T ⊆ A`, the sums `∑ S` and `∑ T` are distinct subset sums
    (strict monotonicity), so the divisibility-free condition on `subsetSums A`
    forbids each from dividing the other. -/
theorem subsetSum_not_dvd_of_ssubset {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    {S T : Finset ℕ} (hS : S.Nonempty) (hST : S ⊂ T) (hTA : T ⊆ A) :
    ¬(S.sum id ∣ T.sum id) ∧ ¬(T.sum id ∣ S.sum id) := by
  have hSA : S ⊆ A := subset_trans hST.subset hTA
  have hTne : T.Nonempty := Finset.Nonempty.mono hST.subset hS
  have hne : S.sum id ≠ T.sum id := ne_of_lt (subsetSum_lt_of_ssubset hA hST hTA)
  exact hA.2 (S.sum id) (subsetSum_mem hSA hS) (T.sum id) (subsetSum_mem hTA hTne) hne

/-- **No proper non-empty subset sum divides the total.**  Specialising the chain
    statement to `T = A`: for every `∅ ≠ S ⊊ A`, `¬(∑ S ∣ ∑ A)`.  This is the
    uniform strengthening of the sibling file's per-element result. -/
theorem proper_subset_not_dvd_total {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    {S : Finset ℕ} (hS : S.Nonempty) (hSA : S ⊂ A) :
    ¬(S.sum id ∣ A.sum id) :=
  (subsetSum_not_dvd_of_ssubset hA hS hSA (Finset.Subset.refl A)).1

/-- The sibling's headline `validSubset_elem_not_dvd_sum` recovered as the
    singleton case: for `|A| ≥ 2`, no element `a ∈ A` divides the total `∑ A`.
    Indeed `{a} ⊊ A` (a second element exists), and `∑ {a} = a`. -/
theorem elem_not_dvd_total {n : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    (hcard : 1 < A.card) {a : ℕ} (ha : a ∈ A) : ¬(a ∣ A.sum id) := by
  have hss : ({a} : Finset ℕ) ⊂ A := by
    rw [Finset.ssubset_iff_of_subset (Finset.singleton_subset_iff.mpr ha)]
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
    exact ⟨b, hb, Finset.notMem_singleton.mpr hba⟩
  have h := proper_subset_not_dvd_total hA (Finset.singleton_nonempty a) hss
  simpa using h

end Erdos882OQ03OQ02
