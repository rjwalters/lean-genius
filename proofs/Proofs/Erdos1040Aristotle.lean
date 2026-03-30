/-
  Aristotle targets for Erdős Problem #1040
  Routine supporting lemmas for automated proof search.
  See Erdos1040Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, non-negativity, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

namespace Erdos1040

/-
## Definitions (copied from Erdos1040Problem.lean for self-containment)
-/

/-- The n-th diameter of a set F. -/
noncomputable def nthDiameter (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {(∏ i in Finset.range n, ∏ j in Finset.range i,
    Complex.abs (pts i - pts j)) ^ (2 / (n * (n - 1) : ℝ)) |
    pts : Fin n → ℂ // ∀ i, pts i ∈ F}

/-- The transfinite diameter (logarithmic capacity) of F. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  ⨅ n : ℕ, nthDiameter F n

/-- A polynomial with roots in F. -/
structure PolynomialInF (F : Set ℂ) where
  degree : ℕ
  roots : Fin degree → ℂ
  roots_in_F : ∀ i, roots i ∈ F

variable {F : Set ℂ}

noncomputable def PolynomialInF.eval (p : PolynomialInF F) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

def sublevelSet (p : PolynomialInF F) : Set ℂ :=
  {z : ℂ | Complex.abs (p.eval z) < 1}

noncomputable def sublevelMeasure (p : PolynomialInF F) : ℝ≥0∞ :=
  MeasureTheory.volume (sublevelSet p)

noncomputable def mu (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (p : PolynomialInF F), sublevelMeasure p

/-- Corrected μ: restricted to degree ≥ 1 (the original includes degree-0
    which has empty sublevel set, making mu = 0 trivially). -/
noncomputable def mu_pos_degree (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (p : PolynomialInF F) (_ : p.degree > 0), sublevelMeasure p

/-
## Aristotle targets: basic properties of transfinite diameter

These are standard results in potential theory (Fekete 1923, Ransford 1995).
-/

/-- Transfinite diameter is monotone: F ⊆ G → ρ(F) ≤ ρ(G).
    Proof idea: nthDiameter F n ≤ nthDiameter G n (sSup over subset),
    then iInf preserves ≤.
    BLOCKER: requires BddAbove for the value set, which needs G bounded
    or a more careful treatment of the sSup. -/
theorem transfiniteDiameter_mono (F G : Set ℂ) (h : F ⊆ G) :
    transfiniteDiameter F ≤ transfiniteDiameter G := by
  sorry

/-- Transfinite diameter is non-negative.
    Proof idea: nthDiameter is sSup of non-negative reals (x^(2/k) ≥ 0),
    so sSup ≥ 0 (returns 0 for empty/unbounded sets in ℝ),
    and iInf over [0,∞) is ≥ 0 via le_ciInf.
    BLOCKER: the not-BddAbove case of sSup requires accessing ℝ's
    implementation detail (sSup returns 0 when ¬(Nonempty ∧ BddAbove)). -/
theorem transfiniteDiameter_nonneg (F : Set ℂ) :
    transfiniteDiameter F ≥ 0 := by
  sorry

/-- μ_pos(F) is achieved or approached for infinite F.
    Uses the corrected definition (degree ≥ 1). -/
theorem mu_pos_degree_infimum (F : Set ℂ) (hF : F.Infinite) :
    ∀ ε > 0, ∃ (p : PolynomialInF F), p.degree > 0 ∧
      sublevelMeasure p < mu_pos_degree F + ε := by
  sorry

end Erdos1040
