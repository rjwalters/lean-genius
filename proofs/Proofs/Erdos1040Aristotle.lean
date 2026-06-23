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
  exact Real.rpow_nonneg (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => Complex.abs.nonneg _) _

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
    Each |pts i - pts j| ≤ diam(G), so the product ≤ (diam G + 1)^(n*n).
    For n ≤ 1 the rpow exponent is 0 giving value 1.
    For n ≥ 2 the exponent ≤ 1 so rpow ≤ product ≤ (diam G + 1)^(n*n).
    Proof adapted from Erdos1040Problem.lean transfiniteDiameter_mono_of_bounded. -/
theorem nthDiameter_bddAbove_of_bounded (G : Set ℂ) (hG : Bornology.IsBounded G) (n : ℕ) :
    BddAbove {(∏ i : Fin n, ∏ j in Finset.Iio i,
      Complex.abs (pts i - pts j)) ^ (2 / (n * (n - 1) : ℝ)) |
      pts : Fin n → ℂ // ∀ i, pts i ∈ G} := by
  refine ⟨(Metric.diam G + 1) ^ (n * n), ?_⟩
  rintro _ ⟨⟨pts, hpts⟩, rfl⟩
  have hD1 : (1 : ℝ) ≤ Metric.diam G + 1 := by linarith [Metric.diam_nonneg (s := G)]
  -- Each factor: |pts i - pts j| ≤ diam G + 1
  have hfac : ∀ i j : Fin n, Complex.abs (pts i - pts j) ≤ Metric.diam G + 1 := by
    intro i j
    have h1 : Complex.abs (pts i - pts j) = dist (pts i) (pts j) := by
      rw [← Complex.dist_eq]
    rw [h1]; linarith [Metric.dist_le_diam_of_mem hG (hpts i) (hpts j)]
  -- Product ≤ (diam G + 1)^(n*n)
  have hprod_le : ∏ i : Fin n, ∏ j in Finset.Iio i,
      Complex.abs (pts i - pts j) ≤ (Metric.diam G + 1) ^ (n * n) := by
    calc ∏ i : Fin n, ∏ j in Finset.Iio i, Complex.abs (pts i - pts j)
        ≤ ∏ i : Fin n, (Metric.diam G + 1) ^ (Finset.Iio i).card := by
          apply Finset.prod_le_prod
          · intro i _; exact Finset.prod_nonneg fun j _ => Complex.abs.nonneg _
          · intro i _
            have : ∏ j in Finset.Iio i, Complex.abs (pts i - pts j) ≤
                ∏ _j in Finset.Iio i, (Metric.diam G + 1) :=
              Finset.prod_le_prod (fun j _ => Complex.abs.nonneg _) (fun j _ => hfac i j)
            rwa [Finset.prod_const] at this
      _ = (Metric.diam G + 1) ^ ∑ i : Fin n, (Finset.Iio i).card :=
          Finset.prod_pow_eq_pow_sum Finset.univ _ _
      _ ≤ (Metric.diam G + 1) ^ (n * n) := by
          apply pow_le_pow_right₀ hD1
          calc ∑ i : Fin n, (Finset.Iio i).card
              ≤ ∑ _i : Fin n, n :=
                Finset.sum_le_sum fun i _ =>
                  (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n)
            _ = n * n := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  -- Apply rpow bound
  have hprod_nn : 0 ≤ ∏ i : Fin n, ∏ j in Finset.Iio i, Complex.abs (pts i - pts j) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => Complex.abs.nonneg _
  rcases le_or_gt n 1 with hn1 | hn2
  · -- n ≤ 1: exponent = 0, value = 1 ≤ (D+1)^(n*n)
    have he0 : (2 : ℝ) / ((↑n : ℝ) * ((↑n : ℝ) - 1)) = 0 := by
      have : n = 0 ∨ n = 1 := by omega; rcases this with rfl | rfl <;> norm_num
    rw [he0, Real.rpow_zero]; exact one_le_pow₀ hD1
  · -- n ≥ 2: exponent ∈ (0, 1], so product^e ≤ max(product, 1) ≤ (D+1)^(n*n)
    have he_le : (2 : ℝ) / ((↑n : ℝ) * ((↑n : ℝ) - 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h1 : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn2
      nlinarith [show (1 : ℝ) ≤ (↑n : ℝ) - 1 by linarith]
    rcases le_or_gt (∏ i : Fin n, ∏ j in Finset.Iio i, Complex.abs (pts i - pts j)) 1
      with hle1 | hgt1
    · exact (Real.rpow_le_one hprod_nn hle1 (by positivity)).trans (one_le_pow₀ hD1)
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt hgt1) he_le).trans
        (Real.rpow_one _ ▸ hprod_le)

/-- **Scaling: nthDiameter(c·F, n) = |c| · nthDiameter(F, n).**

**FALSE for n ≤ 1**: When n = 0 or n = 1, the inner product over `Finset.Iio i`
is empty, giving product = 1. The exponent is 2/(n*(n-1)) = 2/0 = 0, so
`1 ^ 0 = 1` regardless of F or c. Thus `nthDiameter(cF, n) = 1` but
`|c| * nthDiameter(F, n) = |c| * 1 = |c| ≠ 1` for |c| ≠ 1.

The correct statement requires `n ≥ 2`. -/
theorem nthDiameter_scale (F : Set ℂ) (c : ℂ) (n : ℕ) (hn : n ≥ 2) :
    nthDiameter ((fun z => c * z) '' F) n = Complex.abs c * nthDiameter F n := by sorry

/-- **Scaling of transfinite diameter — FALSE with inf-over-all-n definition.**

The `transfiniteDiameter` definition uses `⨅ n : ℕ, nthDiameter F n`. Since
`nthDiameter F 0 = nthDiameter F 1 = 1` for all F, the inf is clamped at ≤ 1.
For sets with true transfinite diameter > 1 (e.g., disc of radius 2), scaling
by c with `|c| < 1` gives `transfiniteDiameter(cF) = 1 ≠ |c| * 1`.

Fix: define transfiniteDiameter as `⨅ n ≥ 2, nthDiameter F n` or use
`Filter.liminf`. See `transfiniteDiameter'` in Erdos1040Problem.lean. -/
-- theorem transfiniteDiameter_scale (F : Set ℂ) (c : ℂ) (hc : c ≠ 0) :
--     transfiniteDiameter ((fun z => c * z) '' F) =
--     Complex.abs c * transfiniteDiameter F := by sorry

end Erdos1040
