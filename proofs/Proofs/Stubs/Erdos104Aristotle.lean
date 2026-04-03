/-
  Aristotle targets for Erdős Problem #104
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos104Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open conjecture (o(n²) unit circles with 3+ points)
  - NOT theorems depending on axiomatized background results
  - Routine geometric distance facts and membership facts
  - No definition sorries
  - No axioms

  Included targets (5):
  - dist_nonneg: dist p q ≥ 0
  - dist_self: dist p p = 0
  - dist_comm: dist p q = dist q p
  - circle_contains_zero: CircleContainsKPoints c P 0 (trivially)
  - filter_le_card: (P.filter ...).card ≤ P.card
-/
import Mathlib

namespace Erdos104Aristotle

open Finset

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def dist' (p q : Point) : ℝ := ‖p - q‖

structure UnitCircle where
  center : Point

def OnCircle (p : Point) (c : UnitCircle) : Prop := dist' p c.center = 1

-- Routine: dist' is nonneg.
-- The norm of any vector is nonneg.
theorem dist_nonneg (p q : Point) : dist' p q ≥ 0 := by
  sorry

-- Routine: dist' to self is 0.
-- ‖p - p‖ = ‖0‖ = 0.
theorem dist_self (p : Point) : dist' p p = 0 := by
  sorry

-- Routine: dist' is symmetric.
-- ‖p - q‖ = ‖-(q - p)‖ = ‖q - p‖.
theorem dist_comm (p q : Point) : dist' p q = dist' q p := by
  sorry

-- Routine: 0 points on any circle (trivially).
-- 0 ≤ card of any filter.
theorem circle_contains_zero (c : UnitCircle) (P : Finset Point) :
    0 ≤ (P.filter fun p => dist' p c.center = 1).card := by
  sorry

-- Routine: filter count is at most total count.
-- Finset.card_filter_le.
theorem filter_le_card (P : Finset Point) (c : UnitCircle) :
    (P.filter fun p => dist' p c.center = 1).card ≤ P.card := by
  sorry

end Erdos104Aristotle
