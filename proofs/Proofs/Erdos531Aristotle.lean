/-
  Aristotle targets for Erdős Problem #531 (Folkman's Theorem)
  Routine supporting lemmas and small case proofs for automated proof search.
  See Erdos531Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem (growth rate of F(k))
  - Small concrete cases: F(1) = 1, F(2) = 3
  - Supporting structural lemmas about SubsetSums and MonochromaticSubsetSums
  - Clean theorem statements with no definition sorries
  - No axioms (folkman_theorem and balogh_2017 are NOT included here)

  Mathematical context:
  F(k) = minimal N such that any 2-coloring of {1,...,N} contains a k-element
  set A where all non-empty subset sums are monochromatic.

  F(1) = 1: trivially, any element a is a monochromatic 1-element set (SubsetSums {a} = {a}).
  F(2) = 3: the pair {1,2} needs {1,2,3} all same color; N=2 is insufficient.
-/
import Mathlib

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

/- ## Supporting Structural Lemmas -/

/-- The subset sums of a singleton {n} equals {n}. -/
lemma subsetSums_singleton (n : ℕ) : SubsetSums {n} = {n} := by
  sorry

/-- Every 1-element set has monochromatic subset sums (trivially). -/
lemma monochromaticSubsetSums_singleton (c : Coloring) (n : ℕ) :
    MonochromaticSubsetSums c {n} := by
  sorry

/-- For any coloring, the single-element set {1} witnesses ExistsMonochromaticSet 1 1. -/
lemma one_mem_validN_one : 1 ∈ ValidN 1 := by
  sorry

/-- N = 0 is not in ValidN 1 since {1,...,0} = ∅ has no 1-element subsets. -/
lemma zero_not_mem_validN_one : 0 ∉ ValidN 1 := by
  sorry

/-- Every element of ValidN 1 is at least 1. -/
lemma validN_one_lower_bound : ∀ n ∈ ValidN 1, 1 ≤ n := by
  sorry

/- ## Small Cases -/

/-- F(1) = 1: Any 1-element subset of {1} trivially has monochromatic subset sums. -/
theorem F_1 : F 1 = 1 := by
  sorry

/-- F(2) = 3: Need {1,2,3} to guarantee monochromatic {a, b, a+b}.
    The coloring c(1)=T, c(2)=F shows N=2 is insufficient.
    For N=3: any 2-coloring forces some pair with all sums monochromatic. -/
theorem F_2 : F 2 = 3 := by
  sorry

end Erdos531Aristotle
