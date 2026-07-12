/-
# Erdős Problem #882 — OQ-03-OQ-03: The antichain necessary condition is sharp exactly at size two

Erdős Problem #882 asks for the largest `A ⊆ {1,…,n}` whose non-empty subset
sums are pairwise non-dividing (answer: `(1+o(1)) log₂ n`).  The sibling file
`Erdos882ProblemOQ03OQ01` proves a one-directional structural fact:

  * `validSubset_antichain` — **every valid set is a divisibility antichain**
    (`ValidSubset n A ⟹ DivisibilityFree A`).

That is a *necessary* condition extracted for free from the constraint on subset
sums.  This file asks the converse question — *when is being an antichain also
sufficient?* — and pins the answer down completely at the two smallest sizes:

  * `validSubset_pair_iff` — **for a two-element set the antichain condition is
    exactly validity**: `ValidSubset n {a,b} ↔ ¬(a ∣ b) ∧ ¬(b ∣ a)` (given the
    range bounds).  This is the *converse* of `validSubset_antichain` in the base
    case: for pairs, the only obstruction to feasibility is the elements dividing
    one another.  The proof computes the whole sum set `subsetSums {a,b} =
    {a, b, a+b}` (`subsetSums_pair`) and checks the three unordered pairs — the
    two "shift" pairs `{a, a+b}`, `{b, a+b}` reduce to the same divisibilities as
    `{a, b}` because `a ∣ a+b ↔ a ∣ b`, while `a+b` divides neither `a` nor `b`
    for size reasons.

  * `antichain_not_sufficient` — **at size three the converse already fails**:
    `{2,3,5}` is a divisibility antichain (`2∤3, 2∤5, 3∤5`) yet is *not* valid for
    any `n`, because `2 = ∑{2}` and `8 = ∑{3,5}` are both subset sums and `2 ∣ 8`.
    So `validSubset_antichain` cannot be upgraded to an iff beyond `|A| = 2`; the
    subset-sum condition is strictly stronger than the element-level antichain
    condition from three elements on.

  * `validSubset_two_three` — a concrete positive witness: `{2,3}` is valid for
    every `n ≥ 3`.

Self-contained: the four predicates are re-declared here using the modern Finset
API (the original parent `Erdos882Problem.lean` predates the current Mathlib
toolchain and no longer builds), so this contribution stands on its own.

Reference: Erdős Problem #882, https://erdosproblems.com/882
-/

import Mathlib

namespace Erdos882OQ03OQ03

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

/-- Every non-empty subset `S ⊆ A` contributes its sum `∑ S` to `subsetSums A`. -/
theorem subsetSum_mem {A S : Finset ℕ} (hSA : S ⊆ A) (hS : S.Nonempty) :
    S.sum id ∈ subsetSums A := by
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨S, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hSA, Finset.nonempty_iff_ne_empty.mp hS⟩

/-- Every element of `A` is a subset sum of `A` (the sum of the singleton `{a}`). -/
theorem self_mem_subsetSums {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∈ subsetSums A := by
  have := subsetSum_mem (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a)
  simpa using this

/-- A non-empty subset of a two-element set is one of the three obvious ones. -/
theorem nonempty_subset_pair {a b : ℕ} {S : Finset ℕ}
    (hS : S ⊆ ({a, b} : Finset ℕ)) (hne : S.Nonempty) :
    S = {a} ∨ S = {b} ∨ S = {a, b} := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · refine Or.inr (Or.inr (Finset.Subset.antisymm hS ?_))
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · refine Or.inl (Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr ha))
    intro x hx
    have hx' := hS hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · simp
    · exact absurd hx hb
  · refine Or.inr (Or.inl (Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hb)))
    intro x hx
    have hx' := hS hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · exact absurd hx ha
    · simp
  · obtain ⟨x, hx⟩ := hne
    have hx' := hS hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · exact absurd hx ha
    · exact absurd hx hb

/-- **The subset-sum set of a pair is `{a, b, a+b}`.**  The non-empty subsets of
    `{a,b}` are exactly `{a}`, `{b}`, `{a,b}`, whose sums are `a`, `b`, `a+b`. -/
theorem subsetSums_pair {a b : ℕ} (hab : a ≠ b) :
    subsetSums ({a, b} : Finset ℕ) = {a, b, a + b} := by
  apply Finset.Subset.antisymm
  · intro m hm
    unfold subsetSums nonemptySubsets at hm
    rw [Finset.mem_image] at hm
    obtain ⟨S, hS, rfl⟩ := hm
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSne⟩ := hS
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
    rcases nonempty_subset_pair hSsub hne with h | h | h <;>
      subst h <;> simp [Finset.sum_pair hab]
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact self_mem_subsetSums (by simp)
    · exact self_mem_subsetSums (by simp)
    · have := subsetSum_mem (Finset.Subset.refl ({a, b} : Finset ℕ))
        ⟨a, by simp⟩
      simpa [Finset.sum_pair hab] using this

/-- **For a two-element set, being a divisibility antichain is exactly validity.**
    The converse of `validSubset_antichain` (`Erdos882ProblemOQ03OQ01`) in the
    base case: subject to the range bounds, the *only* obstruction to a pair being
    feasible is one element dividing the other.  The "shift" pairs `{a, a+b}` and
    `{b, a+b}` in the sum set `{a, b, a+b}` reduce to the same two divisibilities
    (`a ∣ a+b ↔ a ∣ b`), and `a+b` divides neither `a` nor `b`. -/
theorem validSubset_pair_iff {n a b : ℕ} (hab : a ≠ b)
    (ha : 1 ≤ a ∧ a ≤ n) (hb : 1 ≤ b ∧ b ≤ n) :
    ValidSubset n ({a, b} : Finset ℕ) ↔ ¬(a ∣ b) ∧ ¬(b ∣ a) := by
  constructor
  · intro hV
    have haS : a ∈ subsetSums ({a, b} : Finset ℕ) := self_mem_subsetSums (by simp)
    have hbS : b ∈ subsetSums ({a, b} : Finset ℕ) := self_mem_subsetSums (by simp)
    exact hV.2 a haS b hbS hab
  · rintro ⟨hnab, hnba⟩
    -- positivity is needed to rule out `a+b ∣ a` etc.
    have hapos : 0 < a := ha.1
    have hbpos : 0 < b := hb.1
    -- `a + b` divides neither `a` nor `b`.
    have hab_a : ¬ (a + b) ∣ a := fun h => by
      have := Nat.le_of_dvd hapos h; omega
    have hab_b : ¬ (a + b) ∣ b := fun h => by
      have := Nat.le_of_dvd hbpos h; omega
    -- `a ∣ a+b ↔ a ∣ b` and `b ∣ a+b ↔ b ∣ a`.
    have ha_shift : ¬ a ∣ (a + b) := fun h =>
      hnab ((Nat.dvd_add_right (dvd_refl a)).mp h)
    have hb_shift : ¬ b ∣ (a + b) := fun h =>
      hnba ((Nat.dvd_add_left (dvd_refl b)).mp h)
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · rw [subsetSums_pair hab]
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxy
          | exact ⟨hnab, hnba⟩
          | exact ⟨hnba, hnab⟩
          | exact ⟨ha_shift, hab_a⟩
          | exact ⟨hab_a, ha_shift⟩
          | exact ⟨hb_shift, hab_b⟩
          | exact ⟨hab_b, hb_shift⟩

/-- A concrete positive witness: `{2,3}` is valid for every `n ≥ 3`
    (`2 ∤ 3`, `3 ∤ 2`). -/
theorem validSubset_two_three {n : ℕ} (hn : 3 ≤ n) :
    ValidSubset n ({2, 3} : Finset ℕ) :=
  (validSubset_pair_iff (by norm_num) ⟨by norm_num, by omega⟩ ⟨by norm_num, hn⟩).mpr
    ⟨by norm_num, by norm_num⟩

/-- `{2,3,5}` is a divisibility antichain: no element divides another. -/
theorem divisibilityFree_two_three_five :
    DivisibilityFree ({2, 3, 5} : Finset ℕ) := by
  unfold DivisibilityFree; decide

/-- **`{2,3,5}` is not valid for any `n`.**  Both `2 = ∑{2}` and `8 = ∑{3,5}`
    are subset sums, and `2 ∣ 8`, so `subsetSums {2,3,5}` is not divisibility-free
    even though the set itself is an antichain. -/
theorem not_validSubset_two_three_five (n : ℕ) :
    ¬ ValidSubset n ({2, 3, 5} : Finset ℕ) := by
  intro hV
  have h2 : (2 : ℕ) ∈ subsetSums ({2, 3, 5} : Finset ℕ) :=
    self_mem_subsetSums (by simp)
  have h8 : (8 : ℕ) ∈ subsetSums ({2, 3, 5} : Finset ℕ) := by
    have hmem := subsetSum_mem
      (show ({3, 5} : Finset ℕ) ⊆ ({2, 3, 5} : Finset ℕ) by decide)
      (⟨3, by decide⟩ : ({3, 5} : Finset ℕ).Nonempty)
    simpa [Finset.sum_pair (by norm_num : (3 : ℕ) ≠ 5)] using hmem
  exact (hV.2 2 h2 8 h8 (by norm_num)).1 (by norm_num)

/-- **The antichain necessary condition is not sufficient beyond size two.**
    `{2,3,5}` is a three-element divisibility antichain that is not valid for any
    `n`.  Together with `validSubset_pair_iff` (validity `↔` antichain at size two)
    this shows the equivalence in `validSubset_antichain` is sharp: it upgrades to
    an iff exactly for `|A| ≤ 2`. -/
theorem antichain_not_sufficient :
    ∃ A : Finset ℕ, A.card = 3 ∧ DivisibilityFree A ∧ ∀ n, ¬ ValidSubset n A :=
  ⟨{2, 3, 5}, by decide, divisibilityFree_two_three_five, not_validSubset_two_three_five⟩

/-! ## Validity is a hereditary set system (independence system)

Beyond the base-case sharpness above, `ValidSubset n` has a clean *structural*
shape: it is **downward closed** — every subset of a valid set is valid — and it
**only grows** as the ambient range `n` widens.  Together with the trivial base
cases (`∅` and every in-range singleton are valid) this exhibits the valid
subsets of `{1,…,n}` as an *independence system* (abstract simplicial complex).
The extremal `(1+o(1))·log₂ n` bound of Erdős #882 is exactly the maximal-face
size of this complex; the lemmas here are the elementary closure properties that
any such bound implicitly relies on. -/

/-- **`subsetSums` is monotone in the ground set.**  Enlarging `A` to `B ⊇ A` can
    only add subset sums: every non-empty subset of `A` is a non-empty subset of
    `B`, so it still contributes its sum. -/
theorem subsetSums_mono {A B : Finset ℕ} (h : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  intro m hm
  unfold subsetSums nonemptySubsets at hm ⊢
  rw [Finset.mem_image] at hm ⊢
  obtain ⟨S, hS, rfl⟩ := hm
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS.1.trans h, hS.2⟩

/-- **`DivisibilityFree` is inherited by subsets.**  Being a divisibility
    antichain is a downward-closed property. -/
theorem DivisibilityFree.subset {S T : Finset ℕ} (hT : DivisibilityFree T)
    (hST : S ⊆ T) : DivisibilityFree S :=
  fun a ha b hb hab => hT a (hST ha) b (hST hb) hab

/-- **Validity is downward closed.**  Every subset `B ⊆ A` of a valid set is
    itself valid: the range bounds pass to elements of `B`, and
    `subsetSums B ⊆ subsetSums A` (`subsetSums_mono`) keeps the sum set
    divisibility-free (`DivisibilityFree.subset`).  This makes the valid subsets
    of `{1,…,n}` an independence system. -/
theorem validSubset_subset {n : ℕ} {A B : Finset ℕ} (hA : ValidSubset n A)
    (hBA : B ⊆ A) : ValidSubset n B :=
  ⟨fun a ha => hA.1 a (hBA ha), hA.2.subset (subsetSums_mono hBA)⟩

/-- **Validity is monotone in the range `n`.**  Widening the ambient interval
    `{1,…,n}` never destroys validity: the divisibility-free condition on the sum
    set does not mention `n`, and the only `n`-dependent clause is the upper bound
    `a ≤ n`, which is preserved when `n` increases. -/
theorem validSubset_mono_n {n m : ℕ} {A : Finset ℕ} (hA : ValidSubset n A)
    (hnm : n ≤ m) : ValidSubset m A :=
  ⟨fun a ha => ⟨(hA.1 a ha).1, (hA.1 a ha).2.trans hnm⟩, hA.2⟩

/-- The empty set is valid for every `n`: it has no elements and its sum set is
    empty, so both clauses hold vacuously.  (The empty face of the complex.) -/
theorem validSubset_empty (n : ℕ) : ValidSubset n (∅ : Finset ℕ) := by
  refine ⟨by simp, ?_⟩
  have hsub : subsetSums (∅ : Finset ℕ) = ∅ := by
    unfold subsetSums nonemptySubsets; simp
  rw [hsub]
  intro a ha; simp at ha

/-- Every in-range singleton `{a}` (with `1 ≤ a ≤ n`) is valid: its only non-empty
    subset is `{a}` itself, so every subset sum equals `a` and the one-element sum
    set is vacuously divisibility-free.  (The vertices of the complex.) -/
theorem validSubset_singleton {n a : ℕ} (ha : 1 ≤ a ∧ a ≤ n) :
    ValidSubset n ({a} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact ha
  · have hmem : ∀ m ∈ subsetSums ({a} : Finset ℕ), m = a := by
      intro m hm
      unfold subsetSums nonemptySubsets at hm
      rw [Finset.mem_image] at hm
      obtain ⟨S, hS, rfl⟩ := hm
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      obtain ⟨hSsub, hSne⟩ := hS
      have hSa : S = {a} := by
        rw [Finset.subset_singleton_iff] at hSsub
        rcases hSsub with h | h
        · exact absurd h hSne
        · exact h
      subst hSa; simp
    intro x hx y hy hxy
    exact absurd ((hmem x hx).trans (hmem y hy).symm) hxy

end Erdos882OQ03OQ03
