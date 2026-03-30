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

/-- The n-th diameter of a set F.
    The product is over all pairs (i, j) with j < i < n. -/
noncomputable def nthDiameter (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {(∏ i : Fin n, ∏ j in Finset.Iio i,
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

/-- Corrected μ(F): infimum over polynomials of degree ≥ 1. -/
noncomputable def muPosDeg (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (p : PolynomialInF F) (_ : p.degree ≥ 1), sublevelMeasure p

/-
## Aristotle targets: basic properties of transfinite diameter

These are standard results in potential theory (Fekete 1923, Ransford 1995).
-/

/-- Each nthDiameter is non-negative: sSup of non-negative reals ≥ 0.
    Key lemmas: Real.sSup_nonneg, Real.rpow_nonneg, Finset.prod_nonneg, Complex.abs.nonneg -/
theorem nthDiameter_nonneg (F : Set ℂ) (n : ℕ) : 0 ≤ nthDiameter F n := by
  unfold nthDiameter
  apply Real.sSup_nonneg
  rintro _ ⟨⟨pts, _⟩, rfl⟩
  apply Real.rpow_nonneg
  apply Finset.prod_nonneg
  intro i _
  apply Finset.prod_nonneg
  intro j _
  exact Complex.abs.nonneg _

/-- **NOTE**: `transfiniteDiameter_mono` was removed from Aristotle targets.
    It is unprovable with the current `ℝ`-valued `nthDiameter` definition because
    `sSup` returns 0 for unbounded-above sets. For F ⊆ G with G unbounded,
    the value set for G is not BddAbove, so `nthDiameter G n = 0`, while
    `nthDiameter F n` can be positive (e.g., F = {0,1}, G = ℂ, n = 2).
    Fix requires either `EReal`/`ℝ≥0∞`-valued nthDiameter or a BddAbove hypothesis.
    See Erdos1040Problem.lean for a bounded version. -/

/-- Transfinite diameter is non-negative: iInf of non-negative values ≥ 0.
    Key lemma: Real.iInf_nonneg -/
theorem transfiniteDiameter_nonneg (F : Set ℂ) :
    transfiniteDiameter F ≥ 0 := by
  unfold transfiniteDiameter
  exact Real.iInf_nonneg (fun n => nthDiameter_nonneg F n)

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

/-
## Aristotle targets: boundedness and scaling

These are needed to fill sorries in Erdos1040Problem.lean.
-/

/-- When G is bounded, the nthDiameter value set is BddAbove.
    Key: each |pts i - pts j| ≤ diam(G), so the product is bounded,
    and rpow with exponent 2/(n*(n-1)) gives ≤ diam(G).
    Uses: Metric.isBounded_iff, Finset.prod_le_prod, Real.rpow_le_rpow -/
theorem nthDiameter_bddAbove_of_bounded (G : Set ℂ) (hG : Bornology.IsBounded G) (n : ℕ) :
    BddAbove {(∏ i : Fin n, ∏ j in Finset.Iio i,
      Complex.abs (pts i - pts j)) ^ (2 / (n * (n - 1) : ℝ)) |
      pts : Fin n → ℂ // ∀ i, pts i ∈ G} := by sorry

/-- Scaling: nthDiameter(c·F, n) = |c| · nthDiameter(F, n).
    Proof: |c·x - c·y| = |c|·|x-y|, factor |c|^(n*(n-1)/2) out of product,
    rpow simplifies exponent to give |c|^1 = |c|. Then factor |c| out of sSup.
    Uses: Complex.abs.map_mul, Finset.prod_mul_distrib, Real.mul_rpow -/
theorem nthDiameter_scale (F : Set ℂ) (c : ℂ) (n : ℕ) :
    nthDiameter ((fun z => c * z) '' F) n = Complex.abs c * nthDiameter F n := by sorry

/-- Scaling property of transfinite diameter: ρ(cF) = |c|·ρ(F).
    Follows from nthDiameter_scale and pulling constant out of iInf.
    Uses: nthDiameter_scale, Real.iInf_mul_of_nonneg (or similar) -/
theorem transfiniteDiameter_scale (F : Set ℂ) (c : ℂ) (hc : c ≠ 0) :
    transfiniteDiameter ((fun z => c * z) '' F) =
    Complex.abs c * transfiniteDiameter F := by sorry

end Erdos1040
