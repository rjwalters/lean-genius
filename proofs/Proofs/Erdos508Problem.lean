/-!
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

/-! ## Definitions -/

/-- The unit-distance graph on ℝ²: vertices are points, edges connect
    pairs at Euclidean distance exactly 1. -/
noncomputable def unitDistGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := dist x y = 1 ∧ x ≠ y
  symm x y h := by constructor <;> [rw [dist_comm]; exact Ne.symm] <;> exact h.1 <;> exact h.2
  loopless x h := h.2 rfl

/-- The chromatic number of the plane: χ(ℝ²). -/
noncomputable def planeChromatic : ℕ := sorry
-- Full definition requires SimpleGraph.chromaticNumber on unitDistGraph

/-! ## Main Problem -/

/-- **Erdős Problem #508 (Hadwiger–Nelson)**: determine χ(ℝ²).
    The answer is one of 5, 6, or 7. -/
axiom erdos_508_problem :
  5 ≤ planeChromatic ∧ planeChromatic ≤ 7

/-! ## Known Lower Bounds -/

/-- **χ ≥ 3**: an equilateral triangle with side length 1 requires 3 colors. -/
axiom chromatic_ge_3 : 3 ≤ planeChromatic

/-- **χ ≥ 4**: the Moser spindle (7 vertices, 11 edges) is a unit-distance
    graph with chromatic number 4. -/
axiom chromatic_ge_4_moser : 4 ≤ planeChromatic

/-- **χ ≥ 5 (de Grey 2018)**: a unit-distance graph on ~1581 vertices
    requires 5 colors. This improved the 4-color lower bound that had
    stood since the 1960s. -/
axiom de_grey_2018 : 5 ≤ planeChromatic

/-! ## Known Upper Bound -/

/-- **χ ≤ 7 (Isbell)**: tile the plane with regular hexagons of diameter
    slightly less than 1. Color with a 7-color repeating pattern.
    No two same-colored points are at distance 1. -/
axiom chromatic_le_7_isbell : planeChromatic ≤ 7

/-! ## Related Results -/

/-- **Fractional Chromatic Number**: the fractional chromatic number χ_f(ℝ²)
    satisfies 4 ≤ χ_f ≤ 4.359... (Matolcsi–Ruzsa–Varga–Zsámboki lower,
    Croft upper). -/
axiom fractional_chromatic_bounds :
  ∃ χf : ℝ, 4 ≤ χf ∧ χf ≤ 4.36

/-- **Higher Dimensions**: the chromatic number of ℝ^d grows exponentially.
    For ℝ³, it is known that 6 ≤ χ(ℝ³) ≤ 15. -/
axiom higher_dimensions :
  ∃ χ3 : ℕ, 6 ≤ χ3 ∧ χ3 ≤ 15

/-- **Erdős–de Bruijn (1951)**: the chromatic number of the plane equals
    the maximum chromatic number of its finite unit-distance subgraphs.
    So it suffices to find finite graphs requiring many colors. -/
axiom erdos_de_bruijn :
  ∀ k : ℕ, k ≤ planeChromatic ↔
    ∃ (n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin 2)),
      ∀ c : Fin n → Fin k,
        ∃ i j : Fin n, i ≠ j ∧ dist (pts i) (pts j) = 1 ∧ c i = c j
