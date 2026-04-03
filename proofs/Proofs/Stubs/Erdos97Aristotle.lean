/-
  Aristotle targets for Erdős Problem #97
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos97Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open question (k=4 equidistant conjecture)
  - NOT theorems depending on danzerPoints (def-sorry)
  - Routine distance properties and filter monotonicity
  - No definition sorries
  - No axioms

  Included targets (5):
  - dist'_nonneg: dist' p q ≥ 0 (norm is nonneg)
  - dist'_self: dist' p p = 0
  - dist'_comm: dist' p q = dist' q p (norm is symmetric)
  - hasKEquidistant_zero: hasKEquidistantAt 0 A p for any A, p (trivially)
  - filter_card_le: filter card ≤ card of the whole set
-/
import Mathlib

namespace Erdos97Aristotle

open Finset

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def dist' (p q : Point) : ℝ := ‖p - q‖

-- Routine: dist' is nonneg.
-- The norm of any vector is nonneg.
theorem dist'_nonneg (p q : Point) : dist' p q ≥ 0 := by
  sorry

-- Routine: dist' to self is 0.
-- ‖p - p‖ = ‖0‖ = 0.
theorem dist'_self (p : Point) : dist' p p = 0 := by
  sorry

-- Routine: dist' is symmetric.
-- ‖p - q‖ = ‖q - p‖ since ‖-v‖ = ‖v‖.
theorem dist'_comm (p q : Point) : dist' p q = dist' q p := by
  sorry

-- Routine: 0-equidistant is vacuously true.
-- Any p in any set A has 0 ≤ card of any filter.
theorem hasKEquidistant_zero (A : Finset Point) (p : Point) :
    ∃ r : ℝ, r > 0 ∧ 0 ≤ (A.filter fun q => dist' p q = r).card := by
  sorry

-- Routine: filter card ≤ card of original finset.
-- Standard Finset.card_filter_le.
theorem filter_card_le (A : Finset Point) (r : ℝ) (p : Point) :
    (A.filter fun q => dist' p q = r).card ≤ A.card := by
  sorry

end Erdos97Aristotle
