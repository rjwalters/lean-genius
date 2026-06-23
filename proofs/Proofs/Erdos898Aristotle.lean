/-
  Aristotle targets for Erdős Problem #898 (Erdős-Mordell Inequality)
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos898Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the Erdős-Mordell inequality itself (proven via axiom)
  - NOT theorems depending on IsInteriorPoint, perpendicularFoot, incenter (def-sorrys)
  - Routine distance facts and triangle structural properties
  - No definition sorries
  - No axioms

  Included targets (5):
  - dist_nonneg: dist P Q ≥ 0
  - dist_self: dist P P = 0
  - dist_comm: dist P Q = dist Q P
  - isEquilateral_symm: IsEquilateral A B C → IsEquilateral B A C
  - vertexDistanceSum_nonneg: vertexDistanceSum P A B C ≥ 0
-/
import Mathlib

namespace Erdos898Aristotle

open EuclideanSpace

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def dist (P Q : Point) : ℝ := ‖P - Q‖

def IsEquilateral (A B C : Point) : Prop :=
  dist A B = dist B C ∧ dist B C = dist A C

noncomputable def vertexDistanceSum (P A B C : Point) : ℝ :=
  dist P A + dist P B + dist P C

-- Routine: dist P Q ≥ 0.
-- The norm of any vector is nonneg.
theorem dist_nonneg (P Q : Point) : dist P Q ≥ 0 := by
  sorry

-- Routine: dist P P = 0.
-- ‖P - P‖ = ‖0‖ = 0.
theorem dist_self (P : Point) : dist P P = 0 := by
  sorry

-- Routine: dist is symmetric.
-- ‖P - Q‖ = ‖-(Q - P)‖ = ‖Q - P‖.
theorem dist_comm (P Q : Point) : dist P Q = dist Q P := by
  sorry

-- Routine: IsEquilateral is symmetric in first two arguments.
-- Swap the first two vertices of the equilateral triangle.
theorem isEquilateral_swap12 (A B C : Point) (h : IsEquilateral A B C) :
    IsEquilateral B A C := by
  sorry

-- Routine: vertexDistanceSum is nonneg.
-- Sum of nonneg values is nonneg.
theorem vertexDistanceSum_nonneg (P A B C : Point) :
    vertexDistanceSum P A B C ≥ 0 := by
  sorry

end Erdos898Aristotle
