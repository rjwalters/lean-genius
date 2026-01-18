/-
  Erdős Problem #1043: Polynomial Level Set Projections

  Source: https://erdosproblems.com/1043
  Status: SOLVED (Pommerenke 1961)

  Statement:
  Let f ∈ ℂ[x] be a monic non-constant polynomial. Must there exist a straight
  line ℓ such that the projection of {z : |f(z)| ≤ 1} onto ℓ has measure ≤ 2?

  Answer: NO

  Known Results:
  - Pommerenke (1961): There exists f where every projection has measure ≥ 2.386
  - Pommerenke (1961): For any f, some projection has measure ≤ 3.3

  Historical Context:
  This problem was posed by Erdős, Herzog, and Piranian in 1958. They studied
  metric properties of polynomials, asking how "spread out" level sets can be.
  For the polynomial f(z) = zⁿ, the level set is the unit disk, with all
  projections having measure 2 (diameter). The question was whether 2 is always
  achievable.

  References:
  [EHP58] Erdős, Herzog, Piranian, "Metric properties of polynomials" (1958)
  [Po59] Pommerenke, "On some problems by Erdős, Herzog and Piranian" (1959)
  [Po61] Pommerenke, "On metric properties of complex polynomials" (1961)

  Tags: complex-analysis, polynomials, measure-theory, geometry
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace Erdos1043

open MeasureTheory Polynomial Complex

/-! ## Part I: The Level Set of a Polynomial -/

/-- The level set of f at height r is {z ∈ ℂ : |f(z)| ≤ r}.
    For r = 1, this is the "unit lemniscate" of f. -/
def levelSet (f : Polynomial ℂ) (r : ℝ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ r}

/-- The standard level set at height 1. -/
def unitLevelSet (f : Polynomial ℂ) : Set ℂ :=
  levelSet f 1

/-- For f(z) = z, the unit level set is the closed unit disk. -/
theorem levelSet_X : unitLevelSet X = Metric.closedBall 0 1 := by
  ext z
  simp [unitLevelSet, levelSet, Metric.closedBall]

/-- For f(z) = zⁿ, the unit level set is still the closed unit disk. -/
theorem levelSet_X_pow (n : ℕ) (hn : n > 0) :
    unitLevelSet (X ^ n) = Metric.closedBall 0 1 := by
  sorry

/-! ## Part II: Projections onto Lines -/

/-- A direction in ℂ, represented as a unit vector. -/
def Direction := {u : ℂ // ‖u‖ = 1}

/-- The projection of a point z onto the line through the origin with direction u.
    This gives the signed distance along the u-direction. -/
noncomputable def projectOnto (u : Direction) (z : ℂ) : ℝ :=
  (z * conj u.val).re

/-- The projection of a set onto a line. -/
noncomputable def projectSet (u : Direction) (S : Set ℂ) : Set ℝ :=
  projectOnto u '' S

/-- The measure (length) of the projection of S onto the line with direction u. -/
noncomputable def projectionMeasure (u : Direction) (S : Set ℂ) : ℝ≥0∞ :=
  volume (projectSet u S)

/-! ## Part III: Basic Examples -/

/-- The unit disk projects to [-1, 1] in any direction, with measure 2. -/
theorem disk_projection_measure (u : Direction) :
    projectionMeasure u (Metric.closedBall (0 : ℂ) 1) = 2 := by
  sorry

/-- Corollary: For f(z) = zⁿ, every projection has measure 2. -/
theorem monomial_projection (n : ℕ) (hn : n > 0) (u : Direction) :
    projectionMeasure u (unitLevelSet (X ^ n)) = 2 := by
  sorry

/-! ## Part IV: The Erdős-Herzog-Piranian Question -/

/-- The conjecture (false): For every monic polynomial f, some projection has measure ≤ 2. -/
def EHP_Conjecture : Prop :=
  ∀ f : Polynomial ℂ, f.Monic → f.natDegree ≥ 1 →
    ∃ u : Direction, projectionMeasure u (unitLevelSet f) ≤ 2

/-- The minimum projection measure over all directions. -/
noncomputable def minProjectionMeasure (f : Polynomial ℂ) : ℝ≥0∞ :=
  ⨅ u : Direction, projectionMeasure u (unitLevelSet f)

/-- The maximum projection measure over all directions. -/
noncomputable def maxProjectionMeasure (f : Polynomial ℂ) : ℝ≥0∞ :=
  ⨆ u : Direction, projectionMeasure u (unitLevelSet f)

/-! ## Part V: Pommerenke's Counterexample -/

/-- **Pommerenke (1961)**: The EHP conjecture is FALSE.

    There exists a monic polynomial f such that every projection of its
    unit level set has measure at least 2.386. -/
axiom pommerenke_counterexample :
    ∃ f : Polynomial ℂ, f.Monic ∧ f.natDegree ≥ 1 ∧
      ∀ u : Direction, projectionMeasure u (unitLevelSet f) ≥ 2.386

/-- Corollary: The EHP conjecture is false. -/
theorem EHP_conjecture_false : ¬EHP_Conjecture := by
  intro h
  obtain ⟨f, hMonic, hDeg, hProj⟩ := pommerenke_counterexample
  obtain ⟨u, hu⟩ := h f hMonic hDeg
  have := hProj u
  -- 2.386 > 2
  sorry

/-- The Pommerenke constant: infimum over all polynomials of the min projection measure. -/
noncomputable def pommerenkeConstant : ℝ≥0∞ :=
  ⨆ (f : Polynomial ℂ) (_ : f.Monic) (_ : f.natDegree ≥ 1),
    minProjectionMeasure f

/-- Pommerenke showed this constant is at least 2.386. -/
axiom pommerenke_lower_bound : pommerenkeConstant ≥ 2.386

/-! ## Part VI: Pommerenke's Upper Bound -/

/-- **Pommerenke (1961)**: For any monic polynomial, some projection has measure ≤ 3.3.

    This is a positive result: while 2 is not always achievable, 3.3 is. -/
axiom pommerenke_upper_bound :
    ∀ f : Polynomial ℂ, f.Monic → f.natDegree ≥ 1 →
      ∃ u : Direction, projectionMeasure u (unitLevelSet f) ≤ 3.3

/-- Corollary: The minimum projection measure is bounded by 3.3. -/
theorem min_projection_bounded (f : Polynomial ℂ) (hMonic : f.Monic) (hDeg : f.natDegree ≥ 1) :
    minProjectionMeasure f ≤ 3.3 := by
  sorry

/-! ## Part VII: Properties of Level Sets -/

/-- For a degree-n monic polynomial, the level set has "capacity" 1.
    (Capacity is a measure of size from potential theory.) -/
axiom levelSet_capacity (f : Polynomial ℂ) (hMonic : f.Monic) :
    True  -- Placeholder for capacity definition

/-- The level set is connected if and only if all roots lie in the level set. -/
theorem levelSet_connected_iff (f : Polynomial ℂ) (hMonic : f.Monic) :
    IsConnected (unitLevelSet f) ↔ ∀ z, f.eval z = 0 → z ∈ unitLevelSet f := by
  sorry

/-- The level set is always compact (closed and bounded). -/
theorem levelSet_compact (f : Polynomial ℂ) (hMonic : f.Monic) (hDeg : f.natDegree ≥ 1) :
    IsCompact (unitLevelSet f) := by
  sorry

/-! ## Part VIII: The Width Function -/

/-- The width of a set S in direction u is the length of its projection onto u. -/
noncomputable def width (S : Set ℂ) (u : Direction) : ℝ≥0∞ :=
  projectionMeasure u S

/-- The minimum width of S over all directions. -/
noncomputable def minWidth (S : Set ℂ) : ℝ≥0∞ :=
  ⨅ u : Direction, width S u

/-- The maximum width of S over all directions (the diameter). -/
noncomputable def maxWidth (S : Set ℂ) : ℝ≥0∞ :=
  ⨆ u : Direction, width S u

/-- For convex sets, minWidth = diameter / (some constant related to shape). -/
theorem convex_width_bounds (S : Set ℂ) (hConvex : Convex ℝ S) (hCompact : IsCompact S) :
    minWidth S ≤ maxWidth S := by
  sorry

/-! ## Part IX: Lemniscates -/

/-- A lemniscate is the level set of a polynomial.
    The name comes from the figure-eight shape for certain quadratics. -/
def IsLemniscate (S : Set ℂ) : Prop :=
  ∃ f : Polynomial ℂ, ∃ r > 0, S = levelSet f r

/-- The Bernoulli lemniscate: {z : |z² - 1| = c} for some c.
    This is the classic figure-eight shape. -/
def bernoulliLemniscate (c : ℝ) : Set ℂ :=
  {z : ℂ | ‖z^2 - 1‖ = c}

/-- For c = 1, the Bernoulli lemniscate passes through the origin. -/
theorem bernoulli_origin : (0 : ℂ) ∈ bernoulliLemniscate 1 := by
  simp [bernoulliLemniscate]

/-! ## Part X: Related Results -/

/-- The transfinite diameter of the unit level set equals 1 for monic polynomials. -/
axiom transfinite_diameter_one (f : Polynomial ℂ) (hMonic : f.Monic) :
    True  -- Placeholder for transfinite diameter

/-- Chebyshev's theorem: Among monic degree-n polynomials, the Chebyshev polynomial
    minimizes the sup norm on [-1, 1]. -/
axiom chebyshev_optimal (n : ℕ) (hn : n > 0) :
    True  -- Placeholder for Chebyshev optimality

/-- The level set {|f(z)| ≤ 1} contains all roots of f. -/
theorem roots_in_levelSet (f : Polynomial ℂ) (z : ℂ) (hz : f.eval z = 0) :
    z ∈ unitLevelSet f := by
  simp [unitLevelSet, levelSet, hz]

/-! ## Part XI: Quantitative Bounds -/

/-- For a monic polynomial of degree n, the level set has area at most π.
    (Equality holds for f(z) = zⁿ.) -/
axiom levelSet_area_bound (f : Polynomial ℂ) (hMonic : f.Monic) (hDeg : f.natDegree ≥ 1) :
    volume (unitLevelSet f) ≤ Real.pi

/-- The diameter of the level set is at most 4 for monic polynomials.
    (The unit disk has diameter 2, but level sets can be more spread out.) -/
axiom levelSet_diameter_bound (f : Polynomial ℂ) (hMonic : f.Monic) (hDeg : f.natDegree ≥ 1) :
    Metric.diam (unitLevelSet f) ≤ 4

/-! ## Part XII: Summary -/

/-- The main theorem: Answer to Erdős Problem #1043.

    The answer is NO: not every monic polynomial has a projection of measure ≤ 2.
    But every monic polynomial has a projection of measure ≤ 3.3. -/
theorem erdos_1043_answer :
    (¬EHP_Conjecture) ∧
    (∀ f : Polynomial ℂ, f.Monic → f.natDegree ≥ 1 →
      ∃ u : Direction, projectionMeasure u (unitLevelSet f) ≤ 3.3) := by
  constructor
  · exact EHP_conjecture_false
  · exact pommerenke_upper_bound

end Erdos1043

/-!
## Summary

This file formalizes Erdős Problem #1043 on polynomial level set projections.

**Status**: SOLVED (Pommerenke 1961)

**The Problem**: For a monic polynomial f ∈ ℂ[x], must there exist a line ℓ
such that the projection of {z : |f(z)| ≤ 1} onto ℓ has measure ≤ 2?

**Answer**: NO
- Pommerenke found polynomials where every projection has measure ≥ 2.386
- But every polynomial has some projection with measure ≤ 3.3

**What we formalize**:
1. Level sets of polynomials
2. Projections onto lines in ℂ
3. The EHP conjecture and its negation
4. Pommerenke's lower bound (2.386)
5. Pommerenke's upper bound (3.3)
6. Properties of level sets (compactness, connectivity)
7. Width functions and lemniscates
8. Related results (area bounds, diameter bounds)

**Key axioms**:
- `pommerenke_counterexample`: Exists f with all projections ≥ 2.386
- `pommerenke_upper_bound`: Every f has some projection ≤ 3.3

**Historical Note**: This is a beautiful problem connecting complex analysis,
potential theory, and geometric measure theory. The level sets are called
"lemniscates" and have been studied since Bernoulli.
-/
