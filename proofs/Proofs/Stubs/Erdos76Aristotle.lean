/-
  Aristotle targets for Erdős Problem #76: Edge-Disjoint Monochromatic Triangles
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos76Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorem (Gruslys-Letzter: every 2-coloring has ≥(1+o(1))n²/12 triangles)
  - NOT theorems depending on axiomatized results (gruslys_letzter, balanced_achieves_bound)
  - Routine properties of Color, triangles, and basic combinatorial bounds
  - No definition sorries
  - No axioms

  Included targets (5):
  - color_cases: every Color is Red or Blue (exhaustive cases)
  - totalTriangles_eq: totalTriangles n = n*(n-1)*(n-2)/6
  - totalEdges_eq: totalEdges n = n*(n-1)/2
  - triangle_card: a Triangle has exactly 3 vertices (by definition)
  - conjecturedBound_pos: conjecturedBound n ≥ 0
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

namespace Erdos76Aristotle

inductive Color
  | Red : Color
  | Blue : Color
  deriving DecidableEq, Repr

noncomputable def conjecturedBound (n : ℕ) : ℝ := (n : ℝ)^2 / 12

def totalTriangles (n : ℕ) : ℕ := Nat.choose n 3

def totalEdges (n : ℕ) : ℕ := Nat.choose n 2

-- Routine: every Color is Red or Blue.
-- Exhaustive case analysis on the Color type.
theorem color_cases (c : Color) : c = Color.Red ∨ c = Color.Blue := by
  sorry

-- Routine: the conjectured bound n²/12 is nonneg.
-- n² ≥ 0 so n²/12 ≥ 0.
theorem conjecturedBound_nonneg (n : ℕ) : 0 ≤ conjecturedBound n := by
  sorry

-- Routine: C(n,2) = n*(n-1)/2.
-- The standard formula for the binomial coefficient.
theorem totalEdges_formula (n : ℕ) : totalEdges n = n * (n - 1) / 2 := by
  sorry

-- Routine: C(n,3) ≤ n^3 for all n.
-- Loose bound: the number of triangles is at most n^3.
theorem totalTriangles_le_cube (n : ℕ) : totalTriangles n ≤ n ^ 3 := by
  sorry

-- Routine: conjecturedBound is monotone.
-- If m ≤ n then m²/12 ≤ n²/12.
theorem conjecturedBound_mono (m n : ℕ) (h : m ≤ n) :
    conjecturedBound m ≤ conjecturedBound n := by
  sorry

end Erdos76Aristotle
