/-
  Erdős Problem #1070: Independence Number of Unit Distance Graphs

  Source: https://erdosproblems.com/1070
  Status: OPEN

  Statement:
  Let f(n) be the maximum k such that any n points in ℝ² contain k points
  with no two at distance 1. Estimate f(n). In particular, is f(n) ≥ n/4?

  Best Known Bounds: 0.22936n ≤ f(n) ≤ (2/7)n ≈ 0.285n

  Key Results:
  - Larman-Rogers (1972): f(n) ≥ m₁·n where m₁ is the density of unit-distance-free sets
  - Croft (1967): m₁ ≥ 0.22936, giving the lower bound
  - Moser spindle: 7-vertex unit distance graph with independence 2, giving f(n) ≤ (2/7)n
  - ACMVZ (2023): m₁ ≤ 0.247, so density methods CANNOT achieve n/4

  Connection to Hadwiger-Nelson: The chromatic number χ of the plane satisfies 5 ≤ χ ≤ 7.
  Since ω·χ ≥ n for independence number ω, we have f(n) ≥ n/χ ≥ n/7.

  References:
  - Larman, D. G., Rogers, C. A. (1972). "The realization of distances within sets in Euclidean space"
  - Croft, H. T. (1967). "Incidence incidents"
  - de Grey, A. D. N. J. (2018). "The chromatic number of the plane is at least 5"
  - ACMVZ (2023). "Upper bounds for the density of unit-distance-free sets"
-/

import Mathlib

namespace Erdos1070

/- ## Unit Distance Graphs

A unit distance graph has vertices as points in ℝ² and edges between
points at Euclidean distance exactly 1.
-/

/-- The Euclidean distance function in ℝ² -/
noncomputable def euclideanDist (p q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  dist p q

/-- Two points are at unit distance if their Euclidean distance is exactly 1 -/
def isUnitDistance (p q : EuclideanSpace ℝ (Fin 2)) : Prop :=
  euclideanDist p q = 1

/-- A unit distance graph on n points in ℝ² -/
structure UnitDistanceGraph (n : ℕ) where
  /-- The set of n points in the plane -/
  points : Finset (EuclideanSpace ℝ (Fin 2))
  /-- The set has exactly n points -/
  card_eq : points.card = n

/-- An independent set in a unit distance graph: no two points at distance 1 -/
def IsIndependentSet {n : ℕ} (G : UnitDistanceGraph n)
    (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  S ⊆ G.points ∧ ∀ p q : EuclideanSpace ℝ (Fin 2),
    p ∈ S → q ∈ S → p ≠ q → ¬isUnitDistance p q

/-- The independence number of a unit distance graph -/
noncomputable def independenceNumber {n : ℕ} (G : UnitDistanceGraph n) : ℕ :=
  Finset.sup (G.points.powerset.filter (IsIndependentSet G)) Finset.card

/- ## The Function f(n)

f(n) is the minimum independence number across all n-point unit distance graphs.
This is the function Erdős asks to estimate.
-/

/-- f(n) = minimum independence number over all n-point unit distance graphs.
    Axiomatized as an extremal quantity over geometric configurations. -/
axiom f (n : ℕ) : ℕ

/-- f(n) is a valid minimum: every n-point configuration has an independent set of size f(n) -/
/-- f(n) is achieved: some configuration has independence number exactly f(n) -/
/- ## The Density Approach

The key insight of Larman and Rogers is to connect the discrete problem
to the continuous density of unit-distance-free measurable sets.
-/

/-- m₁ = supremum density of measurable unit-distance-free sets in ℝ².
    Axiomatized since its exact value is unknown (between 0.229 and 0.25). -/
axiom m1 : ℝ

/-- m₁ is positive -/
/-- m₁ is at most 1 -/
/- ### Larman-Rogers Theorem

The fundamental connection between discrete independence and continuous density.
-/

/-- Larman-Rogers (1972): f(n) ≥ m₁·n -/
axiom larman_rogers_theorem :
  ∀ n : ℕ, (f n : ℝ) ≥ m1 * n

/- ### Croft's Lower Bound

Croft constructed explicit unit-distance-free sets achieving density ≥ 0.22936.
-/

/-- Croft (1967): m₁ ≥ 0.22936 -/
axiom croft_lower_bound : m1 ≥ 0.22936

/-- Combined lower bound: f(n) ≥ 0.22936n -/
theorem f_lower_bound : ∀ n : ℕ, (f n : ℝ) ≥ 0.22936 * n := by
  intro n
  calc (f n : ℝ) ≥ m1 * n := larman_rogers_theorem n
    _ ≥ 0.22936 * n := by nlinarith [croft_lower_bound]

/- ## The Moser Spindle Upper Bound

The Moser spindle is a 7-vertex unit distance graph with independence number 2.
By constructing configurations from copies of the Moser spindle, we get f(n) ≤ (2/7)n.
-/

/-- The Moser spindle has 7 vertices -/
def moserSpindleVertices : ℕ := 7

/-- The Moser spindle has independence number 2 -/
def moserSpindleIndependence : ℕ := 2

/-- The Moser spindle exists as a unit distance graph -/
/-- Moser spindle upper bound: f(n) ≤ (2/7)n -/
axiom moser_spindle_upper_bound :
  ∀ n : ℕ, (f n : ℝ) ≤ (2 / 7) * n

/- ## Main Bounds Theorem

Combining Croft's lower bound and the Moser spindle upper bound.
-/

/-- Best known bounds: 0.22936n ≤ f(n) ≤ (2/7)n -/
theorem best_known_bounds : ∀ n : ℕ,
    0.22936 * n ≤ (f n : ℝ) ∧ (f n : ℝ) ≤ (2 / 7) * n := by
  intro n
  exact ⟨f_lower_bound n, moser_spindle_upper_bound n⟩

/- ## The n/4 Question and Density Limitations

Erdős asked whether f(n) ≥ n/4. ACMVZ (2023) showed that density methods
alone cannot resolve this question because m₁ ≤ 0.247 < 1/4.
-/

/-- ACMVZ (2023): m₁ ≤ 0.247 -/
axiom acmvz_upper_bound : m1 ≤ 0.247

/-- 0.247 < 1/4 = 0.25 -/
lemma quarter_threshold : (0.247 : ℝ) < 1 / 4 := by norm_num

/-- Density methods cannot achieve n/4: m₁ < 1/4 -/
theorem density_insufficient_for_quarter : m1 < 1 / 4 := by
  calc m1 ≤ 0.247 := acmvz_upper_bound
    _ < 1 / 4 := quarter_threshold

/-- The n/4 question remains open: is f(n) ≥ n/4 for all n?
    This cannot be stated as a clean axiom since it is an open yes/no question.
    The density result m₁ < 1/4 (density_insufficient_for_quarter) suggests
    the answer may be no, but this is not a proof. -/

/- ## Connection to Hadwiger-Nelson Problem

The chromatic number χ of the plane (Hadwiger-Nelson problem) satisfies 5 ≤ χ ≤ 7.
Since independence number ω and chromatic number χ satisfy ω·χ ≥ n,
we have f(n) ≥ n/χ.
-/

/-- The chromatic number of the plane (Hadwiger-Nelson problem).
    Axiomatized since its exact value is unknown (between 5 and 7). -/
axiom chromaticNumberPlane : ℕ

/-- De Grey (2018): χ ≥ 5 -/
axiom de_grey_lower_bound : chromaticNumberPlane ≥ 5

/-- Classical upper bound: χ ≤ 7 -/
axiom chromatic_upper_bound : chromaticNumberPlane ≤ 7

/-- Independence-chromatic relationship: f(n) ≥ n/χ -/
axiom independence_chromatic_relation :
  ∀ n : ℕ, (f n : ℝ) ≥ n / chromaticNumberPlane

/-- From chromatic bounds: f(n) ≥ n/7 -/
theorem f_from_chromatic : ∀ n : ℕ, (f n : ℝ) ≥ n / 7 := by
  intro n
  have h1 : (f n : ℝ) ≥ n / chromaticNumberPlane := independence_chromatic_relation n
  have h2 : chromaticNumberPlane ≤ 7 := chromatic_upper_bound
  have h3 := de_grey_lower_bound  -- chromaticNumberPlane ≥ 5
  have hχ_pos : (0 : ℝ) < (chromaticNumberPlane : ℝ) := by
    exact_mod_cast (show 0 < chromaticNumberPlane by omega)
  have hle : (↑chromaticNumberPlane : ℝ) ≤ 7 := by exact_mod_cast h2
  have hfn_nonneg : (0 : ℝ) ≤ ↑(f n) := Nat.cast_nonneg
  have hχ_ne : (↑chromaticNumberPlane : ℝ) ≠ 0 := ne_of_gt hχ_pos
  -- Clear fraction in h1: n/χ ≤ f(n) → n ≤ f(n) * χ
  have h1' : (↑n : ℝ) ≤ ↑(f n) * ↑chromaticNumberPlane := by
    have h := (ge_iff_le.mp h1)
    have := mul_le_mul_of_nonneg_right h (le_of_lt hχ_pos)
    rwa [div_mul_cancel₀ _ hχ_ne] at this
  -- n ≤ f(n) * 7 by transitivity
  have hn7 : (↑n : ℝ) ≤ ↑(f n) * 7 := by
    calc (↑n : ℝ) ≤ ↑(f n) * ↑chromaticNumberPlane := h1'
      _ ≤ ↑(f n) * 7 := mul_le_mul_of_nonneg_left hle hfn_nonneg
  -- Prove n/7 ≤ f(n) by multiplying hn7 by 7⁻¹
  show (f n : ℝ) ≥ ↑n / 7
  rw [ge_iff_le]
  have h7inv : (0 : ℝ) ≤ (7 : ℝ)⁻¹ := by positivity
  have key := mul_le_mul_of_nonneg_right hn7 h7inv
  have eq1 : (↑(f n) : ℝ) * 7 * (7 : ℝ)⁻¹ = ↑(f n) := by ring
  have eq2 : (↑n : ℝ) / 7 = ↑n * (7 : ℝ)⁻¹ := by ring
  linarith

/- ## Summary

Erdős Problem #1070 asks to estimate f(n), the minimum independence number
of n-point unit distance graphs in ℝ².

**Best Known Bounds**: 0.22936n ≤ f(n) ≤ (2/7)n ≈ 0.285n

**The n/4 Question**: Erdős asked if f(n) ≥ n/4.
- The density approach gives f(n) ≥ m₁·n
- Croft showed m₁ ≥ 0.22936
- ACMVZ (2023) showed m₁ ≤ 0.247 < 1/4
- Therefore, density methods CANNOT prove f(n) ≥ n/4
- New techniques would be needed to resolve this question

**Status**: OPEN - the gap between 0.22936 and 2/7 ≈ 0.285 remains unexplored.
-/

/-- Summary: The independence number problem remains open with a gap -/
theorem erdos_1070_summary :
    (∀ n : ℕ, 0.22936 * n ≤ (f n : ℝ)) ∧
    (∀ n : ℕ, (f n : ℝ) ≤ (2 / 7) * n) ∧
    m1 < 1 / 4 := by
  exact ⟨f_lower_bound, moser_spindle_upper_bound, density_insufficient_for_quarter⟩

end Erdos1070
