/-
  Aristotle targets for Erdős Problem #531 (Folkman's Theorem)
  Routine supporting lemmas and small case proofs for automated proof search.
  See Erdos531Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem (growth rate of F(k))
  - Small concrete cases: F(1) = 1, F(2) = 8
  - Supporting structural lemmas about SubsetSums and MonochromaticSubsetSums
  - Clean theorem statements with no definition sorries
  - No axioms (folkman_theorem and balogh_2017 are NOT included here)

  Mathematical context:
  F(k) = minimal N such that any 2-coloring of {1,...,N} contains a k-element
  set A where all non-empty subset sums are monochromatic.

  F(1) = 1: trivially, any element a is a monochromatic 1-element set (SubsetSums {a} = {a}).
  F(2) = 8: an earlier draft of this file claimed F(2) = 3, but that value is
  FALSE for the distinct-pair Folkman number defined here — see the corrected
  proof of `Erdos531.F_2` (2026-07-10) in Erdos531Problem.lean.  All sorries
  below were PROVED (2026-07-23, researcher-1): the definitions here mirror
  `Erdos531`'s verbatim, so the small cases transfer along definitional (`rfl`)
  bridges.
-/
import Mathlib
import Proofs.Erdos531Problem

namespace Erdos531Aristotle

open Finset

/- ## Definitions (mirrored from Erdos531Problem.lean) -/

/-- A two-coloring of natural numbers. -/
def Coloring := ℕ → Bool

/-- The set of all non-empty subset sums of a finite set. -/
def SubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter (· ≠ ∅)).image (Finset.sum · id)

/-- All subset sums have the same color. -/
def MonochromaticSubsetSums (c : Coloring) (A : Finset ℕ) : Prop :=
  ∃ col : Bool, ∀ s ∈ SubsetSums A, c s = col

/-- F(k) existence condition: every 2-coloring of {1,...,N} contains a k-element
    set with monochromatic subset sums. -/
def ExistsMonochromaticSet (N k : ℕ) : Prop :=
  ∀ c : Coloring, ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    MonochromaticSubsetSums c A

/-- The set of valid N values for a given k. -/
def ValidN (k : ℕ) : Set ℕ := {N : ℕ | ExistsMonochromaticSet N k}

/-- F(k) is the minimum valid N. -/
noncomputable def F (k : ℕ) : ℕ := sInf (ValidN k)

/- ## Definitional bridges to `Erdos531`

The definitions above mirror those of `Erdos531Problem.lean` symbol-for-symbol,
so each is *definitionally* equal to its original and the bridges are `rfl`. -/

theorem subsetSums_eq : SubsetSums = Erdos531.SubsetSums := rfl

theorem validN_eq : ValidN = Erdos531.ValidN := rfl

theorem F_eq : F = Erdos531.F := rfl

/- ## Supporting Structural Lemmas -/

/-- The subset sums of a singleton {n} equals {n}. -/
lemma subsetSums_singleton (n : ℕ) : SubsetSums {n} = {n} := by
  ext s
  rw [Finset.mem_singleton]
  constructor
  · intro h
    exact Erdos531.mem_subsetSums_singleton (subsetSums_eq ▸ h)
  · rintro rfl
    unfold SubsetSums
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨{s}, ⟨Finset.Subset.refl _, by simp⟩, by simp⟩

/-- Every 1-element set has monochromatic subset sums (trivially). -/
lemma monochromaticSubsetSums_singleton (c : Coloring) (n : ℕ) :
    MonochromaticSubsetSums c {n} := by
  refine ⟨c n, fun s hs => ?_⟩
  rw [subsetSums_singleton, Finset.mem_singleton] at hs
  rw [hs]

/-- For any coloring, the single-element set {1} witnesses ExistsMonochromaticSet 1 1. -/
lemma one_mem_validN_one : 1 ∈ ValidN 1 := by
  rw [validN_eq]
  exact Erdos531.one_mem_validN_one

/-- N = 0 is not in ValidN 1 since {1,...,0} = ∅ has no 1-element subsets. -/
lemma zero_not_mem_validN_one : 0 ∉ ValidN 1 := by
  intro h
  obtain ⟨A, hcard, hbound, _⟩ := h (fun _ => true)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num)
  have := hbound a ha
  omega

/-- Every element of ValidN 1 is at least 1. -/
lemma validN_one_lower_bound : ∀ n ∈ ValidN 1, 1 ≤ n := by
  intro n hn
  rw [validN_eq] at hn
  exact Erdos531.validN_one_ge_one hn

/- ## Small Cases -/

/-- F(1) = 1: Any 1-element subset of {1} trivially has monochromatic subset sums. -/
theorem F_1 : F 1 = 1 := by
  rw [F_eq]
  exact Erdos531.F_1

/-- F(2) = 8.  **Statement repair (2026-07-23):** this target originally read
    `F 2 = 3` — FALSE for the distinct-pair Folkman number defined here (the
    colouring `3 ↦ R`, everything else `B` defeats all three pairs of
    `{1,2,3}`).  The correct value `8` was established in
    `Erdos531Problem.lean` (`Erdos531.F_2`, corrected 2026-07-10, via the
    256-case `forcedCheck_all` kernel certificate) and transfers along the
    definitional bridge `F_eq`. -/
theorem F_2 : F 2 = 8 := by
  rw [F_eq]
  exact Erdos531.F_2

end Erdos531Aristotle
