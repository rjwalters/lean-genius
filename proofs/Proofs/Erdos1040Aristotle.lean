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

/-
## Aristotle targets: basic properties of transfinite diameter

These are standard results in potential theory (Fekete 1923, Ransford 1995).
-/

/-- Transfinite diameter is monotone: F ⊆ G → ρ(F) ≤ ρ(G).
    Proof idea: nthDiameter F n ≤ nthDiameter G n (sSup over subset),
    then iInf preserves ≤. -/
theorem transfiniteDiameter_mono (F G : Set ℂ) (h : F ⊆ G) :
    transfiniteDiameter F ≤ transfiniteDiameter G := by
  sorry

/-- Transfinite diameter is non-negative.
    Proof idea: nthDiameter is sSup of non-negative reals (x^(2/k) ≥ 0),
    so sSup ≥ 0, and iInf over [0,∞) is ≥ 0. -/
theorem transfiniteDiameter_nonneg (F : Set ℂ) :
    transfiniteDiameter F ≥ 0 := by
  sorry

/-- The uncorrected mu is always 0 (degree-0 bug: constant polynomial 1 has empty sublevel set).
    This makes mu_infimum trivially true. The meaningful version uses muPosDeg (degree ≥ 1). -/
theorem mu_eq_zero (F : Set ℂ) : mu F = 0 := by
  apply le_antisymm
  · have p0 : PolynomialInF F := ⟨0, Fin.elim0, fun i => i.elim0⟩
    calc mu F ≤ sublevelMeasure p0 := iInf_le _ p0
      _ = 0 := by
        simp only [sublevelMeasure, sublevelSet, PolynomialInF.eval]
        convert MeasureTheory.measure_empty
        ext z; simp [Finset.prod_empty, map_one, not_lt.mpr (le_refl _)]
  · exact zero_le _

/-- μ(F) is achieved or approached for infinite F.
    Trivially true because mu F = 0 (degree-0 bug). -/
theorem mu_infimum (F : Set ℂ) (hF : F.Infinite) :
    ∀ ε > 0, ∃ (p : PolynomialInF F), sublevelMeasure p < mu F + ε := by
  intro ε hε
  rw [mu_eq_zero]
  simp only [zero_add]
  exact ⟨⟨0, Fin.elim0, fun i => i.elim0⟩, by
    simp only [sublevelMeasure, sublevelSet, PolynomialInF.eval]
    convert hε using 1
    convert MeasureTheory.measure_empty
    ext z; simp [Finset.prod_empty, map_one, not_lt.mpr (le_refl _)]⟩

end Erdos1040
