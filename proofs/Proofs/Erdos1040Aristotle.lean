/-
  Aristotle targets for Erdős Problem #1040
  Routine supporting lemmas for automated proof search.
  See Erdos1040Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, non-negativity, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Notation note: this file targets Mathlib toolchain v4.26.0, in which the
  `∏ x in s` big-operator syntax and the bundled `Complex.abs` absolute value
  were removed.  We therefore use `∏ x ∈ s` and the norm `‖·‖` throughout
  (`‖z‖ = Complex.abs z` for `z : ℂ`), and write value sets with an explicit
  existential rather than the withdrawn `{ f x | x : T // p x }` binder form.
-/
import Mathlib

open scoped ENNReal

namespace Erdos1040

/-
## Definitions (copied from Erdos1040Problem.lean for self-containment)
-/

/-- The n-th diameter of a set F.
    The product is over all pairs (i, j) with j < i < n. -/
noncomputable def nthDiameter (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ pts : Fin n → ℂ, (∀ i, pts i ∈ F) ∧
    (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖pts i - pts j‖) ^ (2 / (n * (n - 1) : ℝ)) = y}

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
  {z : ℂ | ‖p.eval z‖ < 1}

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
    Key lemmas: Real.sSup_nonneg, Real.rpow_nonneg, Finset.prod_nonneg, norm_nonneg -/
theorem nthDiameter_nonneg (F : Set ℂ) (n : ℕ) : 0 ≤ nthDiameter F n := by
  unfold nthDiameter
  apply Real.sSup_nonneg
  rintro _ ⟨pts, _, rfl⟩
  exact Real.rpow_nonneg (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => norm_nonneg _) _

/- **NOTE**: `transfiniteDiameter_mono` was removed from Aristotle targets.
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

/-- The degree-0 polynomial evaluates to `1` everywhere (empty product), so its
    sublevel set `{z | ‖1‖ < 1}` is empty. -/
theorem degree_zero_sublevel_empty (p : PolynomialInF F) (hp : p.degree = 0) :
    sublevelSet p = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro z
  have h1 : p.eval z = 1 := by
    haveI : IsEmpty (Fin p.degree) := by rw [hp]; infer_instance
    simp [PolynomialInF.eval, Finset.prod_of_isEmpty]
  simp only [sublevelSet, Set.mem_setOf_eq, h1, norm_one, not_lt, le_refl]

/-- The uncorrected mu is always 0 (degree-0 bug: constant polynomial 1 has empty sublevel set).
    This makes mu_infimum trivially true. The meaningful version uses muPosDeg (degree ≥ 1). -/
theorem mu_eq_zero (F : Set ℂ) : mu F = 0 := by
  apply le_antisymm _ (zero_le _)
  calc mu F ≤ sublevelMeasure (⟨0, Fin.elim0, fun i => i.elim0⟩ : PolynomialInF F) :=
        iInf_le _ _
    _ = 0 := by
      rw [sublevelMeasure,
        degree_zero_sublevel_empty (⟨0, Fin.elim0, fun i => i.elim0⟩ : PolynomialInF F) rfl,
        MeasureTheory.measure_empty]

/-- μ(F) is achieved or approached for infinite F.
    Trivially true because mu F = 0 (degree-0 bug). -/
theorem mu_infimum (F : Set ℂ) (hF : F.Infinite) :
    ∀ ε > 0, ∃ (p : PolynomialInF F), sublevelMeasure p < mu F + ε := by
  intro ε hε
  refine ⟨⟨0, Fin.elim0, fun i => i.elim0⟩, ?_⟩
  rw [mu_eq_zero, zero_add, sublevelMeasure,
    degree_zero_sublevel_empty (⟨0, Fin.elim0, fun i => i.elim0⟩ : PolynomialInF F) rfl,
    MeasureTheory.measure_empty]
  exact hε

/-
## Aristotle targets: boundedness and scaling

These are needed to fill sorries in Erdos1040Problem.lean.
-/

/-- When G is bounded, the nthDiameter value set is BddAbove.
    Each ‖pts i - pts j‖ ≤ diam(G), so the product ≤ (diam G + 1)^(n*n).
    For n ≤ 1 the rpow exponent is 0 giving value 1.
    For n ≥ 2 the exponent ≤ 1 so rpow ≤ product ≤ (diam G + 1)^(n*n).
    Proof adapted from Erdos1040Problem.lean transfiniteDiameter_mono_of_bounded. -/
theorem nthDiameter_bddAbove_of_bounded (G : Set ℂ) (hG : Bornology.IsBounded G) (n : ℕ) :
    BddAbove {y : ℝ | ∃ pts : Fin n → ℂ, (∀ i, pts i ∈ G) ∧
      (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖pts i - pts j‖) ^ (2 / (n * (n - 1) : ℝ)) = y} := by
  refine ⟨(Metric.diam G + 1) ^ (n * n), ?_⟩
  rintro _ ⟨pts, hpts, rfl⟩
  have hD1 : (1 : ℝ) ≤ Metric.diam G + 1 := by linarith [Metric.diam_nonneg (s := G)]
  -- Each factor: ‖pts i - pts j‖ ≤ diam G + 1
  have hfac : ∀ i j : Fin n, ‖pts i - pts j‖ ≤ Metric.diam G + 1 := by
    intro i j
    have h1 : ‖pts i - pts j‖ = dist (pts i) (pts j) := (dist_eq_norm _ _).symm
    rw [h1]; linarith [Metric.dist_le_diam_of_mem hG (hpts i) (hpts j)]
  -- Product ≤ (diam G + 1)^(n*n)
  have hprod_le : ∏ i : Fin n, ∏ j ∈ Finset.Iio i,
      ‖pts i - pts j‖ ≤ (Metric.diam G + 1) ^ (n * n) := by
    calc ∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖pts i - pts j‖
        ≤ ∏ i : Fin n, (Metric.diam G + 1) ^ (Finset.Iio i).card := by
          apply Finset.prod_le_prod
          · intro i _; exact Finset.prod_nonneg fun j _ => norm_nonneg _
          · intro i _
            have : ∏ j ∈ Finset.Iio i, ‖pts i - pts j‖ ≤
                ∏ _j ∈ Finset.Iio i, (Metric.diam G + 1) :=
              Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hfac i j)
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
  have hprod_nn : 0 ≤ ∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖pts i - pts j‖ :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => norm_nonneg _
  rcases le_or_gt n 1 with hn1 | hn2
  · -- n ≤ 1: exponent = 0, value = 1 ≤ (D+1)^(n*n)
    have he0 : (2 : ℝ) / ((↑n : ℝ) * ((↑n : ℝ) - 1)) = 0 := by
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> norm_num
    rw [he0, Real.rpow_zero]; exact one_le_pow₀ hD1
  · -- n ≥ 2: exponent ∈ (0, 1], so product^e ≤ max(product, 1) ≤ (D+1)^(n*n)
    have hn2' : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn2
    have hnpos : (0 : ℝ) < (↑n : ℝ) * ((↑n : ℝ) - 1) := by nlinarith
    have he_le : (2 : ℝ) / ((↑n : ℝ) * ((↑n : ℝ) - 1)) ≤ 1 := by
      rw [div_le_one hnpos]
      nlinarith [show (1 : ℝ) ≤ (↑n : ℝ) - 1 by linarith]
    rcases le_or_gt (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖pts i - pts j‖) 1
      with hle1 | hgt1
    · exact (Real.rpow_le_one hprod_nn hle1
        (div_nonneg (by norm_num) (le_of_lt hnpos))).trans (one_le_pow₀ hD1)
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt hgt1) he_le).trans
        (Real.rpow_one _ ▸ hprod_le)

/-- **Scaling: nthDiameter(c·F, n) = ‖c‖ · nthDiameter(F, n).**

**FALSE for n ≤ 1**: When n = 0 or n = 1, the inner product over `Finset.Iio i`
is empty, giving product = 1. The exponent is 2/(n*(n-1)) = 2/0 = 0, so
`1 ^ 0 = 1` regardless of F or c. Thus `nthDiameter(cF, n) = 1` but
`‖c‖ * nthDiameter(F, n) = ‖c‖ * 1 = ‖c‖ ≠ 1` for `‖c‖ ≠ 1`.

The correct statement requires `n ≥ 2`.

Proof: every configuration `pts` valued in `c·F` is `c • x` for a configuration
`x` valued in `F` (choose preimages); scaling every point by `c` multiplies each
pairwise distance by `‖c‖`, hence the pair product by `‖c‖ ^ N` with
`N = ∑ i, #(Iio i) = n(n-1)/2`.  Raising to the power `2/(n(n-1))` multiplies by
`‖c‖ ^ (N · 2/(n(n-1))) = ‖c‖ ^ 1 = ‖c‖`.  So the value set of `c·F` is `‖c‖ •`
the value set of `F`, and `Real.sSup_smul_of_nonneg` (which respects the `sSup`
convention on empty / unbounded sets) finishes. -/
theorem nthDiameter_scale (F : Set ℂ) (c : ℂ) (n : ℕ) (hn : n ≥ 2) :
    nthDiameter ((fun z => c * z) '' F) n = ‖c‖ * nthDiameter F n := by
  have hn1 : 1 ≤ n := by omega
  have hDpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  unfold nthDiameter
  set e : ℝ := 2 / ((n : ℝ) * ((n : ℝ) - 1)) with he
  -- Gauss doubling identity for the number of pairs (j < i) in `Fin n`.
  have hN2 : (∑ i : Fin n, (Finset.Iio i).card) * 2 = n * (n - 1) := by
    have hsum : (∑ i : Fin n, (Finset.Iio i).card) = ∑ i : Fin n, (i : ℕ) :=
      Finset.sum_congr rfl (fun i _ => Fin.card_Iio i)
    rw [hsum, Fin.sum_univ_eq_sum_range (fun k => k) n, Finset.sum_range_id_mul_two n]
  -- Hence `N · e = 1`, where `N = ∑ i, #(Iio i) = n(n-1)/2`.
  have hNe : ((∑ i : Fin n, (Finset.Iio i).card : ℕ) : ℝ) * e = 1 := by
    have hcast : ((∑ i : Fin n, (Finset.Iio i).card : ℕ) : ℝ) * 2
        = (n : ℝ) * ((n : ℝ) - 1) := by
      have h2 : ((∑ i : Fin n, (Finset.Iio i).card : ℕ) : ℝ) * 2
          = (((∑ i : Fin n, (Finset.Iio i).card) * 2 : ℕ) : ℝ) := by push_cast; ring
      rw [h2, hN2]; push_cast [Nat.cast_sub hn1]; ring
    rw [he, ← mul_div_assoc, hcast]
    exact div_self (ne_of_gt hDpos)
  -- Core: scaling every point by `c` multiplies the `e`-th power of the pair
  -- product by exactly `‖c‖` (using `N · e = 1`).
  have key : ∀ x : Fin n → ℂ,
      (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖c * x i - c * x j‖) ^ e
        = ‖c‖ * (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x i - x j‖) ^ e := by
    intro x
    have hfac : ∀ i j : Fin n, ‖c * x i - c * x j‖ = ‖c‖ * ‖x i - x j‖ := by
      intro i j; rw [← mul_sub, norm_mul]
    have hstep : (∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖c * x i - c * x j‖)
        = ‖c‖ ^ (∑ i : Fin n, (Finset.Iio i).card)
          * ∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x i - x j‖ := by
      have h1 : ∀ i : Fin n,
          (∏ j ∈ Finset.Iio i, ‖c * x i - c * x j‖)
            = ‖c‖ ^ (Finset.Iio i).card * ∏ j ∈ Finset.Iio i, ‖x i - x j‖ := by
        intro i
        rw [Finset.prod_congr rfl (fun j _ => hfac i j), Finset.prod_mul_distrib,
          Finset.prod_const]
      rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
    rw [hstep]
    have hPnn : (0 : ℝ) ≤ ∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x i - x j‖ :=
      Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => norm_nonneg _
    have hcnn : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
    rw [Real.mul_rpow (by positivity) hPnn, ← Real.rpow_natCast_mul hcnn, hNe, Real.rpow_one]
  -- The value set of `c · F` is `‖c‖ •` the value set of `F`; conclude via `sSup`.
  rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg (norm_nonneg c)]
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨pts, hpts, rfl⟩
    choose x hxF hxeq using hpts
    refine ⟨(∏ i : Fin n, ∏ j ∈ Finset.Iio i, ‖x i - x j‖) ^ e, ⟨x, hxF, rfl⟩, ?_⟩
    have hpe : pts = fun i => c * x i := funext fun i => (hxeq i).symm
    simp only [smul_eq_mul]
    rw [hpe]
    exact (key x).symm
  · rintro y ⟨v, ⟨x, hxF, rfl⟩, rfl⟩
    refine ⟨fun i => c * x i, fun i => ⟨x i, hxF i, rfl⟩, ?_⟩
    simp only [smul_eq_mul]
    exact key x

end Erdos1040
