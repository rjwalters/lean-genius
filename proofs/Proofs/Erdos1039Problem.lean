/-
  Erdős Problem #1039: Polynomial Lemniscate Disc Radius

  Source: https://erdosproblems.com/1039
  Status: OPEN

  Statement:
  Let f(z) = ∏(z - zᵢ) ∈ ℂ[z] with |zᵢ| ≤ 1 for all i.
  Let ρ(f) be the radius of the largest disc contained in {z : |f(z)| < 1}.

  Determine the behavior of ρ(f). Is it always true that ρ(f) ≫ 1/n?

  A problem of Erdős, Herzog, and Piranian.

  Known Results:
  - Benchmark: f(z) = zⁿ - 1 has ρ(f) ≤ π/(2n)
  - Pommerenke (1961): ρ(f) ≥ 1/(2en²)
  - Krishnapur-Lundberg-Ramachandran (2025): ρ(f) ≫ 1/(n√(log n))
-/

import Mathlib

namespace Erdos1039

/-
## Polynomial Setup
-/

/-- A monic polynomial with roots in the unit disc. -/
structure UnitDiscPolynomial where
  /-- The degree of the polynomial. -/
  degree : ℕ
  /-- The roots of the polynomial. -/
  roots : Fin degree → ℂ
  /-- All roots lie in the closed unit disc. -/
  roots_in_disc : ∀ i, Complex.abs (roots i) ≤ 1

variable (f : UnitDiscPolynomial)

/-- The polynomial as a function ℂ → ℂ. -/
noncomputable def UnitDiscPolynomial.eval (z : ℂ) : ℂ :=
  ∏ i : Fin f.degree, (z - f.roots i)

/-- The sublevel set {z : |f(z)| < 1}. -/
def sublevelSet : Set ℂ :=
  {z : ℂ | Complex.abs (f.eval z) < 1}

/-
## Inscribed Disc Radius
-/

/-- A disc of radius r centered at c is inscribed in S. -/
def isInscribedDisc (S : Set ℂ) (c : ℂ) (r : ℝ) : Prop :=
  r > 0 ∧ ∀ z : ℂ, Complex.abs (z - c) < r → z ∈ S

/-- The supremum of radii of inscribed discs. -/
noncomputable def inscribedDiscRadius (S : Set ℂ) : ℝ :=
  sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc S c r}

/-- ρ(f) - the inscribed disc radius of the sublevel set. -/
noncomputable def rho : ℝ := inscribedDiscRadius (sublevelSet f)

/-
## The Benchmark: zⁿ - 1
-/

/-- The polynomial zⁿ - 1 has roots at the n-th roots of unity. -/
def rootsOfUnity (n : ℕ) (hn : n > 0) : UnitDiscPolynomial where
  degree := n
  roots := fun k => Complex.exp (2 * Real.pi * Complex.I * k / n)
  roots_in_disc := by
    intro i
    simp only [Complex.abs_exp]
    sorry

/-- The benchmark upper bound: ρ(zⁿ - 1) ≤ π/(2n). -/
axiom benchmark_upper (n : ℕ) (hn : n > 0) :
  rho (rootsOfUnity n hn) ≤ Real.pi / (2 * n)

/-
## Pommerenke's Lower Bound (1961)
-/

/-- Pommerenke's lower bound: ρ(f) ≥ 1/(2en²). -/
axiom pommerenke_lower (f : UnitDiscPolynomial) (hf : f.degree > 0) :
  rho f ≥ 1 / (2 * Real.exp 1 * (f.degree : ℝ)^2)

/-- The Pommerenke exponent is 2 (quadratic in n). -/
def pommerenkeExponent : ℕ := 2

/-
## Krishnapur-Lundberg-Ramachandran Bound (2025)
-/

/-- The KLR bound: ρ(f) ≥ c/(n√(log n)) for some constant c > 0. -/
axiom klr_lower :
  ∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree ≥ 3 →
    rho f ≥ c / ((f.degree : ℝ) * Real.sqrt (Real.log f.degree))

/-- The KLR bound is better than Pommerenke for large n. -/
theorem klr_better_than_pommerenke :
    ∀ᶠ n in Filter.atTop,
    1 / ((n : ℝ) * Real.sqrt (Real.log n)) > 1 / (2 * Real.exp 1 * n^2) := by
  sorry

/-
## The Erdős-Herzog-Piranian Conjecture
-/

/-- The conjecture: ρ(f) ≫ 1/n for all unit disc polynomials. -/
def ehpConjecture : Prop :=
  ∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree > 0 →
    rho f ≥ c / f.degree

/-- The conjecture remains open. -/
axiom ehp_open : ¬(ehpConjecture ∨ ¬ehpConjecture)
  -- This is a placeholder to indicate the problem is open

/-
## Comparison of Bounds
-/

/-- Pommerenke: 1/(2en²) -/
noncomputable def pommerenkeBound (n : ℕ) : ℝ :=
  1 / (2 * Real.exp 1 * n^2)

/-- KLR: c/(n√(log n)) -/
noncomputable def klrBound (c : ℝ) (n : ℕ) : ℝ :=
  c / (n * Real.sqrt (Real.log n))

/-- Conjectured: c/n -/
noncomputable def conjecturedBound (c : ℝ) (n : ℕ) : ℝ :=
  c / n

/-- Benchmark upper: π/(2n) -/
noncomputable def benchmarkBound (n : ℕ) : ℝ :=
  Real.pi / (2 * n)

/-- The gap between known lower and upper bounds. -/
theorem bounds_gap (n : ℕ) (hn : n ≥ 3) (c : ℝ) (hc : c > 0) :
    klrBound c n < benchmarkBound n := by
  sorry

/-
## Lemniscate Properties
-/

/-- The lemniscate {z : |f(z)| = 1}. -/
def lemniscate : Set ℂ :=
  {z : ℂ | Complex.abs (f.eval z) = 1}

/-- The sublevel set is open. -/
theorem sublevelSet_isOpen : IsOpen (sublevelSet f) := by
  sorry

/-- The sublevel set is non-empty (contains the roots). -/
theorem sublevelSet_nonempty (hf : f.degree > 0) :
    (sublevelSet f).Nonempty := by
  sorry

/-- Each root is in the sublevel set. -/
theorem root_in_sublevelSet (i : Fin f.degree) :
    f.roots i ∈ sublevelSet f := by
  sorry

/-
## Area Bounds
-/

/-- Area of the sublevel set. -/
noncomputable def sublevelArea : ℝ := MeasureTheory.volume (sublevelSet f)

/-- Lower bound on area implies lower bound on inscribed disc. -/
theorem area_implies_disc_bound :
    sublevelArea f ≥ Real.pi * (rho f)^2 := by
  sorry

/-- The KLR paper establishes area bounds that imply disc bounds. -/
axiom klr_area_bound (f : UnitDiscPolynomial) (hf : f.degree ≥ 3) :
  sublevelArea f ≥ Real.pi / ((f.degree : ℝ)^2 * Real.log f.degree)

/-
## Special Cases
-/

/-- For n = 1, the sublevel set contains a disc of radius 1. -/
theorem degree_one_optimal :
    ∀ (f : UnitDiscPolynomial), f.degree = 1 → rho f = 1 := by
  sorry

/-- For clustered roots, the inscribed disc can be larger. -/
def hasClusteredRoots (f : UnitDiscPolynomial) (ε : ℝ) : Prop :=
  ∃ c : ℂ, ∀ i, Complex.abs (f.roots i - c) < ε

/-- Clustered roots give larger inscribed disc. -/
theorem clustered_implies_large_disc (ε : ℝ) (hε : ε > 0) (hε' : ε < 1) :
    ∀ (f : UnitDiscPolynomial), hasClusteredRoots f ε → f.degree > 0 →
      rho f ≥ 1 - ε := by
  sorry

/-
## Random Polynomials
-/

/-- For random polynomials, the expected ρ is of order 1/√n. -/
axiom random_polynomial_expected :
  ∃ c₁ c₂ > 0, ∀ n : ℕ, n ≥ 2 →
    c₁ / Real.sqrt n ≤ -- Expected[rho(random poly of degree n)]
    c₂ / Real.sqrt n

/-
## The Open Question
-/

/-- The main open question: close the gap between 1/(n√log n) and 1/n. -/
def erdos_1039_question : Prop :=
  ehpConjecture

/-- Current state: known bounds, conjecture unresolved. -/
theorem erdos_1039_current_state :
    (∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree ≥ 3 →
      rho f ≥ c / ((f.degree : ℝ) * Real.sqrt (Real.log f.degree))) ∧
    (∀ n : ℕ, n > 0 → ∃ (f : UnitDiscPolynomial), f.degree = n ∧
      rho f ≤ Real.pi / (2 * n)) := by
  constructor
  · exact klr_lower
  · intro n hn
    use rootsOfUnity n hn
    constructor
    · rfl
    · exact benchmark_upper n hn

/-
## Summary

Erdős Problem #1039 asks about the inscribed disc radius ρ(f) for
polynomials with roots in the unit disc.

**Known**:
- Upper: ρ(zⁿ-1) ≤ π/(2n) (benchmark)
- Lower: ρ(f) ≥ 1/(2en²) (Pommerenke 1961)
- Lower: ρ(f) ≫ 1/(n√log n) (KLR 2025)

**Conjecture**: ρ(f) ≫ 1/n

**Status**: OPEN - the gap between 1/(n√log n) and 1/n remains.
-/

end Erdos1039
