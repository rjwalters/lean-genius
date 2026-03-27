/-
# Erdős Problem #508 — The Hadwiger–Nelson Problem

What is the chromatic number of the plane? That is, what is the minimum
number of colors needed to color ℝ² so that no two points at unit
distance share a color?

## Known Bounds
- χ ≥ 3: equilateral triangle with side 1
- χ ≥ 4: Moser spindle or Golomb graph
- χ ≥ 5: de Grey (2018), using a graph with ~1500 vertices
- χ ≤ 7: hexagonal tiling (Isbell), each hexagon of diameter < 1

The answer is one of {5, 6, 7}.

Status: OPEN
Reference: https://erdosproblems.com/508
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- The unit-distance graph on ℝ²: vertices are points, edges connect
    pairs at Euclidean distance exactly 1. -/
noncomputable def unitDistGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := dist x y = 1 ∧ x ≠ y
  symm x y h := by constructor <;> [rw [dist_comm]; exact Ne.symm] <;> exact h.1 <;> exact h.2
  loopless x h := h.2 rfl

/-- The chromatic number of the plane: χ(ℝ²).
    This is the chromatic number of the unit-distance graph on ℝ².
    Axiomatized since its exact value is the subject of the Hadwiger-Nelson problem. -/
axiom planeChromatic : ℕ

/- ## Main Problem -/

/- ## Known Lower Bounds -/

/- ## Known Upper Bound -/

/- ## Related Results -/
