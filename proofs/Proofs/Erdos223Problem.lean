/-
Erdős Problem #223: Maximum Diameter Pairs (Vázsonyi's Conjecture)

Let d ≥ 2 and n ≥ 2. Define f_d(n) as the maximum number of pairs of points
at distance 1 (the diameter) in any n-point set A ⊆ ℝ^d with diameter 1.

**Question**: Estimate f_d(n).

**Status**: SOLVED

**Results by dimension**:
- d = 2: f₂(n) = n (Hopf-Pannwitz 1934)
- d = 3: f₃(n) = 2n - 2 (Grünbaum, Heppes, Strasziewicz 1956-57)
- d ≥ 4: f_d(n) = ((p-1)/(2p) + o(1))n² where p = ⌊d/2⌋ (Erdős 1960)
- Full characterization: Swanepoel (2009)

Reference: https://erdosproblems.com/223
Originally a conjecture of Vázsonyi.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor.Div

open Finset

namespace Erdos223

/- ## Overview

This problem asks: how many pairs of points can realize the diameter in a
point configuration of diameter 1?

The answer depends dramatically on dimension:
- In 2D: at most n (regular polygon is optimal)
- In 3D: at most 2n-2 (proved independently by three researchers)
- In 4D+: quadratic in n (fundamentally different behavior!)

This is one of Erdős's classic problems in combinatorial geometry.
-/

/- ## Part I: Basic Definitions
-/

/-- A point configuration in d-dimensional Euclidean space. -/
def PointConfig (d n : ℕ) := Fin n → EuclideanSpace ℝ (Fin d)

/-- The distance between two points. -/
noncomputable def pointDist {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  dist x y

/-- The diameter of a configuration: the maximum pairwise distance. -/
noncomputable def diameter {d n : ℕ} (A : PointConfig d n) : ℝ :=
  ⨆ (i j : Fin n), pointDist (A i) (A j)

/-- A configuration has diameter at most r. -/
def hasDiameterAtMost {d n : ℕ} (A : PointConfig d n) (r : ℝ) : Prop :=
  ∀ i j : Fin n, pointDist (A i) (A j) ≤ r

/-- A configuration has diameter exactly r (achievable and bounded). -/
def hasDiameterExactly {d n : ℕ} (A : PointConfig d n) (r : ℝ) : Prop :=
  hasDiameterAtMost A r ∧ ∃ i j : Fin n, i ≠ j ∧ pointDist (A i) (A j) = r

/-- The number of pairs at distance exactly r. -/
noncomputable def countPairsAtDistance {d n : ℕ} (A : PointConfig d n) (r : ℝ) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ pointDist (A p.1) (A p.2) = r)).card

/-- The number of diameter pairs (pairs at the maximum distance). -/
noncomputable def diameterPairs {d n : ℕ} (A : PointConfig d n) : ℕ :=
  countPairsAtDistance A (diameter A)

/- ## Part II: The Function f_d(n)
-/

/-- f_d(n) is the maximum number of diameter pairs over all n-point
    configurations with diameter 1 in ℝ^d. -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (A : PointConfig d n) (_ : hasDiameterExactly A 1), diameterPairs A

/- ## Part III: Two-Dimensional Case (Hopf-Pannwitz 1934)
-/

/-- In 2D, f₂(n) = n exactly.
    The regular n-gon inscribed in a unit circle achieves this. -/
axiom hopf_pannwitz_1934 (n : ℕ) (hn : n ≥ 3) :
  f 2 n = n

/-- The regular n-gon achieves n diameter pairs. -/
def regularPolygonConfig (n : ℕ) : PointConfig 2 n :=
  fun i => ![Real.cos (2 * Real.pi * i.val / n), Real.sin (2 * Real.pi * i.val / n)]

/- ## Part IV: Three-Dimensional Case (1956-57)
-/

/-- In 3D, f₃(n) = 2n - 2.
    Proved independently by Grünbaum, Heppes, and Strasziewicz. -/
axiom three_dimensional_case (n : ℕ) (hn : n ≥ 3) :
  f 3 n = 2 * n - 2

/- ## Part V: Higher Dimensions (Erdős 1960)
-/

/-- For d ≥ 4, f_d(n) grows quadratically in n.
    The coefficient is (p-1)/(2p) where p = ⌊d/2⌋. -/
axiom erdos_1960 (d : ℕ) (hd : d ≥ 4) :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (c₁ : ℝ) * n^2 ≤ f d n ∧ (f d n : ℝ) ≤ c₂ * n^2

/-- The leading coefficient in the quadratic growth. -/
noncomputable def leadingCoefficient (d : ℕ) : ℝ :=
  let p := d / 2
  (p - 1 : ℝ) / (2 * p)

/- ## Part VI: Swanepoel's Complete Solution (2009)
-/

/-- Swanepoel also characterized all extremal configurations. -/
def extremalConfigurationExists (d n : ℕ) : Prop :=
  ∃ A : PointConfig d n, hasDiameterExactly A 1 ∧ diameterPairs A = f d n

/- ## Part VII: Special Cases and Bounds
-/

/-- For d = 4: p = 2, so coefficient is 1/4. -/
theorem four_dimensional_coefficient :
    leadingCoefficient 4 = 1 / 4 := by
  simp [leadingCoefficient]
  norm_num

/-- For d = 5: p = 2, so coefficient is still 1/4. -/
theorem five_dimensional_coefficient :
    leadingCoefficient 5 = 1 / 4 := by
  simp [leadingCoefficient]
  norm_num

/-- For d = 6: p = 3, so coefficient is 1/3. -/
theorem six_dimensional_coefficient :
    leadingCoefficient 6 = 1 / 3 := by
  simp [leadingCoefficient]
  norm_num

/- ## Part VIII: Geometric Interpretation
-/

/-- The diameter graph: vertices are points, edges connect diameter pairs. -/
def diameterGraph {d n : ℕ} (A : PointConfig d n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ pointDist (A i) (A j) = diameter A
  symm := by
    intro i j ⟨hne, hdist⟩
    constructor
    · exact hne.symm
    · simp [pointDist, dist_comm, hdist]
  loopless := by
    intro i ⟨hne, _⟩
    exact hne rfl

/- ## Part IX: Related Problems
-/

/-- **Related: Erdős Problem #132 (Unit Distance Graphs).**
    Instead of maximizing diameter pairs, minimize distinct distances.
    The unit distance problem asks: how many pairs at distance exactly 1
    can an n-point set in ℝ² have? -/
def relatedToUnitDistanceGraphs (n : ℕ) : Prop :=
  ∃ A : PointConfig 2 n,
    countPairsAtDistance A 1 ≥ n^(1 + 1/10 : ℝ).toNat

/-- **Related: Erdős Problem #1084 (Minimum Distance Pairs).**
    Analogous to #223 but for minimum distance: what is the maximum
    number of pairs achieving the minimum distance in an n-point set? -/
def relatedToMinDistanceProblem (d n : ℕ) : Prop :=
  ∃ A : PointConfig d n,
    let minDist := ⨅ (i j : Fin n) (_ : i ≠ j), pointDist (A i) (A j)
    countPairsAtDistance A minDist ≥ n

/- ## Summary

**Erdős Problem #223: SOLVED**

The maximum number of diameter pairs f_d(n) in an n-point configuration
with diameter 1:

| Dimension | Formula | Growth | Solver(s) |
|-----------|---------|--------|-----------|
| d = 2 | f₂(n) = n | Linear | Hopf-Pannwitz (1934) |
| d = 3 | f₃(n) = 2n-2 | Linear | Grünbaum, Heppes, Strasziewicz (1956-57) |
| d ≥ 4 | f_d(n) ~ cn² | Quadratic | Erdős (1960), Swanepoel (2009) |

The transition from linear to quadratic at d = 4 is a fundamental
dimensional phenomenon in combinatorial geometry.
-/

theorem erdos_223_summary :
    -- 2D case
    (∀ n ≥ 3, f 2 n = n) ∧
    -- 3D case
    (∀ n ≥ 3, f 3 n = 2 * n - 2) ∧
    -- Higher dimensional asymptotic
    (∀ d ≥ 4, ∃ c > 0, ∀ n ≥ 2, (f d n : ℝ) ≥ c * n^2) := by
  constructor
  · intro n hn
    exact hopf_pannwitz_1934 n hn
  constructor
  · intro n hn
    exact three_dimensional_case n hn
  · intro d hd
    obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := erdos_1960 d hd
    exact ⟨c₁, hc₁, fun n hn => (h n hn).1⟩

end Erdos223
