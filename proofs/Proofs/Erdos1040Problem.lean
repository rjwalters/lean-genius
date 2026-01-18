/-
  Erdős Problem #1040: Transfinite Diameter and Sublevel Set Measure

  Source: https://erdosproblems.com/1040
  Status: OPEN

  Statement:
  Let F ⊆ ℂ be a closed infinite set, and let μ(F) be the infimum of
  |{z : |f(z)| < 1}| over all polynomials f(z) = ∏(z - zᵢ) with zᵢ ∈ F.

  Is μ(F) determined by the transfinite diameter of F?
  In particular, is μ(F) = 0 whenever the transfinite diameter ≥ 1?

  A problem of Erdős, Herzog, and Piranian.

  Known Results:
  - Answer is YES for line segments and discs (EHP 1958)
  - When transfinite diameter < 1, sublevel set contains disc of radius ≫_F 1
  - Erdős-Netanyahu (1973): bounded connected F with 0 < ρ(F) < 1 → disc bound
-/

import Mathlib

namespace Erdos1040

/-
## Transfinite Diameter (Logarithmic Capacity)
-/

/-- The n-th diameter of a set F. -/
noncomputable def nthDiameter (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {(∏ i in Finset.range n, ∏ j in Finset.range i,
    Complex.abs (pts i - pts j)) ^ (2 / (n * (n - 1) : ℝ)) |
    pts : Fin n → ℂ // ∀ i, pts i ∈ F}

/-- The transfinite diameter (logarithmic capacity) of F. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  ⨅ n : ℕ, nthDiameter F n

/-- Alternative definition using limit. -/
noncomputable def transfiniteDiameter' (F : Set ℂ) : ℝ :=
  Filter.liminf (fun n => nthDiameter F n) Filter.atTop

/-- The two definitions agree. -/
axiom transfiniteDiameter_eq (F : Set ℂ) :
  transfiniteDiameter F = transfiniteDiameter' F

/-
## Polynomials with Roots in F
-/

/-- A polynomial with roots in F. -/
structure PolynomialInF (F : Set ℂ) where
  /-- The degree of the polynomial. -/
  degree : ℕ
  /-- The roots of the polynomial. -/
  roots : Fin degree → ℂ
  /-- All roots lie in F. -/
  roots_in_F : ∀ i, roots i ∈ F

variable {F : Set ℂ}

/-- Evaluate the polynomial at z. -/
noncomputable def PolynomialInF.eval (p : PolynomialInF F) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

/-- The sublevel set {z : |f(z)| < 1}. -/
def sublevelSet (p : PolynomialInF F) : Set ℂ :=
  {z : ℂ | Complex.abs (p.eval z) < 1}

/-- The measure (Lebesgue measure) of the sublevel set. -/
noncomputable def sublevelMeasure (p : PolynomialInF F) : ℝ≥0∞ :=
  MeasureTheory.volume (sublevelSet p)

/-
## The Function μ(F)
-/

/-- μ(F) = infimum of sublevel set measures. -/
noncomputable def mu (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (p : PolynomialInF F), sublevelMeasure p

/-- μ(F) as a real number (when finite). -/
noncomputable def muReal (F : Set ℂ) : ℝ :=
  (mu F).toReal

/-
## The Main Conjecture
-/

/-- Is μ(F) determined by the transfinite diameter? -/
def muDeterminedByDiameter : Prop :=
  ∀ F G : Set ℂ, IsClosed F → F.Infinite →
    IsClosed G → G.Infinite →
    transfiniteDiameter F = transfiniteDiameter G →
    mu F = mu G

/-- The specific conjecture: μ(F) = 0 when transfinite diameter ≥ 1. -/
def diameterOneConjecture : Prop :=
  ∀ F : Set ℂ, IsClosed F → F.Infinite →
    transfiniteDiameter F ≥ 1 →
    mu F = 0

/-- The problem is open. -/
axiom problem_open : ¬(diameterOneConjecture ∨ ¬diameterOneConjecture)

/-
## Known Results: Line Segments and Discs
-/

/-- A line segment in ℂ. -/
def isLineSegment (F : Set ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ F = Set.Icc a b

/-- A closed disc in ℂ. -/
def isClosedDisc (F : Set ℂ) : Prop :=
  ∃ c : ℂ, ∃ r > 0, F = Metric.closedBall c r

/-- For line segments, μ is determined by transfinite diameter. -/
axiom lineSegment_determined (F : Set ℂ) (hF : isLineSegment F) :
  ∃ f : ℝ → ℝ≥0∞, mu F = f (transfiniteDiameter F)

/-- For discs, μ is determined by transfinite diameter. -/
axiom disc_determined (F : Set ℂ) (hF : isClosedDisc F) :
  ∃ f : ℝ → ℝ≥0∞, mu F = f (transfiniteDiameter F)

/-- Line segment of length L has transfinite diameter L/4. -/
axiom lineSegment_diameter (a b : ℂ) :
  transfiniteDiameter (Set.Icc a b) = Complex.abs (b - a) / 4

/-- Disc of radius r has transfinite diameter r. -/
axiom disc_diameter (c : ℂ) (r : ℝ) (hr : r > 0) :
  transfiniteDiameter (Metric.closedBall c r) = r

/-
## Small Transfinite Diameter: Disc in Sublevel Set
-/

/-- When transfinite diameter < 1, sublevel sets contain a disc. -/
axiom small_diameter_disc (F : Set ℂ) (hF : IsClosed F) (hFi : F.Infinite) :
  transfiniteDiameter F < 1 →
  ∃ c > 0, ∀ (p : PolynomialInF F), p.degree > 0 →
    ∃ z₀ : ℂ, ∃ r > 0, r ≥ c ∧
      Metric.ball z₀ r ⊆ sublevelSet p

/-- The constant depends on F. -/
noncomputable def discConstant (F : Set ℂ) : ℝ :=
  sSup {c : ℝ | c > 0 ∧ ∀ (p : PolynomialInF F), p.degree > 0 →
    ∃ z₀ : ℂ, ∃ r ≥ c, Metric.ball z₀ r ⊆ sublevelSet p}

/-
## Erdős-Netanyahu Result (1973)
-/

/-- For bounded connected F with 0 < ρ(F) < 1, get explicit disc bound. -/
axiom erdos_netanyahu (F : Set ℂ) (hF : IsClosed F) (hFi : F.Infinite)
    (hFb : Bornology.IsBounded F) (hFc : IsConnected F) :
  0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
  ∃ r : ℝ → ℝ, (∀ c ∈ Set.Ioo 0 1, r c > 0) ∧
    ∀ (p : PolynomialInF F), p.degree > 0 →
      ∃ z₀ : ℂ, Metric.ball z₀ (r (transfiniteDiameter F)) ⊆ sublevelSet p

/-
## Relationship to Problem 1039
-/

/-- Connection to Problem 1039: unit disc is a special case. -/
def unitDiscCase : Prop :=
  let F := Metric.closedBall (0 : ℂ) 1
  transfiniteDiameter F = 1 ∧
  -- Problem 1039 asks about ρ(f) for this F
  True

theorem unitDisc_diameter : transfiniteDiameter (Metric.closedBall (0 : ℂ) 1) = 1 := by
  have := disc_diameter 0 1 (by norm_num : (1 : ℝ) > 0)
  simp at this
  exact this

/-
## Properties of Transfinite Diameter
-/

/-- Transfinite diameter is monotone. -/
theorem transfiniteDiameter_mono (F G : Set ℂ) (h : F ⊆ G) :
    transfiniteDiameter F ≤ transfiniteDiameter G := by
  sorry

/-- Transfinite diameter is non-negative. -/
theorem transfiniteDiameter_nonneg (F : Set ℂ) :
    transfiniteDiameter F ≥ 0 := by
  sorry

/-- Finite sets have transfinite diameter 0. -/
theorem finite_diameter_zero (F : Set ℂ) (hF : F.Finite) :
    transfiniteDiameter F = 0 := by
  sorry

/-- Scaling property. -/
theorem transfiniteDiameter_scale (F : Set ℂ) (c : ℂ) (hc : c ≠ 0) :
    transfiniteDiameter ((fun z => c * z) '' F) =
    Complex.abs c * transfiniteDiameter F := by
  sorry

/-
## Properties of μ
-/

/-- μ is monotone in F. -/
theorem mu_mono (F G : Set ℂ) (h : F ⊆ G) :
    mu G ≤ mu F := by
  sorry

/-- For infinite F, μ(F) is achieved or approached. -/
theorem mu_infimum (F : Set ℂ) (hF : F.Infinite) :
    ∀ ε > 0, ∃ (p : PolynomialInF F), sublevelMeasure p < mu F + ε := by
  sorry

/-
## The Open Question
-/

/-- The main question: is μ(F) = 0 when ρ(F) ≥ 1? -/
def erdos_1040_question : Prop := diameterOneConjecture

/-- Current state: known for special cases, open in general. -/
theorem erdos_1040_current_state :
    (∀ F : Set ℂ, isLineSegment F ∨ isClosedDisc F →
      transfiniteDiameter F ≥ 1 → mu F = 0) ∧
    (∀ F : Set ℂ, IsClosed F → F.Infinite →
      transfiniteDiameter F < 1 → mu F > 0) := by
  sorry

/-
## Summary

Erdős Problem #1040 asks whether the infimum μ(F) of sublevel set
measures is determined by the transfinite diameter of F.

**Known**:
- YES for line segments and discs (EHP 1958)
- When ρ(F) < 1, sublevel sets contain a disc of positive radius
- Erdős-Netanyahu (1973): explicit bounds for bounded connected sets

**Conjecture**: μ(F) = 0 when transfinite diameter ≥ 1

**Status**: OPEN - the general case remains unresolved.
-/

end Erdos1040
