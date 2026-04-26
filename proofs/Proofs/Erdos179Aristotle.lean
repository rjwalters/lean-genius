/-
  Aristotle targets for Erdős Problem #179
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos179Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorems (Fox-Pohoata, Question1, Question2)
  - NOT theorems depending on F (def-sorry in supersaturation_exists)
  - Routine facts about arithmetic progressions and Finset operations
  - No definition sorries
  - No axioms

  Included targets (5):
  - ap_range_subset: image of range is a Finset ℕ
  - ap_length_one: length-1 AP equals {a}
  - ap_contains_start: start element a ∈ arithmeticProgression a d k for k ≥ 1
  - contains_ap_superset: ContainsAP is upward-closed under ⊆
  - super_prop_mono: SupersaturationProperty is monotone in M (decreasing)
-/
import Mathlib

namespace Erdos179Aristotle

open Finset

def arithmeticProgression (a d : ℕ) (k : ℕ) : Finset ℕ :=
  Finset.image (fun i => a + i * d) (Finset.range k)

def ContainsAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ arithmeticProgression a d k ⊆ A

-- Routine: A length-1 AP is a singleton.
-- image (fun i => a + i * d) (range 1) = {a + 0 * d} = {a}.
theorem ap_length_one (a d : ℕ) :
    arithmeticProgression a d 1 = {a} := by
  sorry

-- Routine: The start element is in the AP.
-- For k ≥ 1, 0 ∈ range k, so a = a + 0 * d ∈ image.
theorem ap_contains_start (a d k : ℕ) (hk : k ≥ 1) :
    a ∈ arithmeticProgression a d k := by
  sorry

-- Routine: ContainsAP is upward-closed under set inclusion.
-- If A ⊆ B and A contains a k-AP, then B contains a k-AP.
theorem contains_ap_superset (A B : Finset ℕ) (k : ℕ)
    (hA : ContainsAP A k) (hAB : A ⊆ B) : ContainsAP B k := by
  sorry

-- Routine: If d > 0, all elements of the AP are ≥ a.
-- a + i * d ≥ a for all i ≥ 0.
theorem ap_ge_start (a d k : ℕ) (hd : d > 0) (i : ℕ) (hi : i < k) :
    a ≤ a + i * d := by
  sorry

-- Routine: Length-0 AP is empty.
-- range 0 = ∅, so image of range 0 is ∅.
theorem ap_length_zero (a d : ℕ) :
    arithmeticProgression a d 0 = ∅ := by
  sorry

end Erdos179Aristotle
