/-
  Power Mean Crossing Zero: M_r ≤ GM ≤ M_s for r < 0 < s
  Open Question: amgm-inequality-oq-03-oq-02-oq-01

  The power mean M_r(z,w) = (∑ wᵢ zᵢ^r)^(1/r) is monotone in r. The same-sign
  cases (0 < r ≤ s and r ≤ s < 0) are proved in AmgmInequalityOQ03. This file
  proves the **crossing zero case**: r < 0 < s → M_r ≤ weightedGeomMean ≤ M_s.

  ## Strategy: Direct AM-GM Application

  The key inequality is: GM(z,w)^r ≤ ∑ wᵢ zᵢ^r for all r ∈ ℝ.
  Proof: Apply the AM-GM inequality (Real.geom_mean_le_arith_mean_weighted) with pᵢ = zᵢ^r:
    ∏ (zᵢ^r)^wᵢ ≤ ∑ wᵢ · (zᵢ^r)
  The LHS equals GM^r (since (∏ zᵢ^wᵢ)^r = ∏ (zᵢ^wᵢ)^r = ∏ zᵢ^(wᵢr) = ∏ (zᵢ^r)^wᵢ).

  From GM^r ≤ ∑ wᵢ zᵢ^r:
  - For r > 0: raise to 1/r > 0 (preserves ≤): GM ≤ M_r
  - For r < 0: raise to 1/r < 0 (reverses ≤): M_r ≤ GM

  This avoids limit arguments entirely. No new Mathlib infrastructure needed.

  ## Main Results

  - `geomMean_rpow_le_weightedSum_rpow`: GM^r ≤ ∑ wᵢ zᵢ^r (for all r)
  - `geom_mean_le_power_mean_pos`: GM ≤ M_r for r > 0 (extends to all r > 0, not just r ≥ 1)
  - `power_mean_le_geom_mean_neg`: M_r ≤ GM for r < 0
  - `power_mean_monotone_crossing_zero`: M_r ≤ M_s for r < 0 < s (fully proved)
-/

import Proofs.AmgmInequalityOQ03
import Mathlib.Tactic

open Real Finset

namespace PowerMeanCrossZero

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

-- ============================================================
-- §1. HELPER LEMMAS
-- ============================================================

/-- The weighted sum ∑ wᵢ zᵢ^r > 0 when weights sum to 1 and all zᵢ > 0. -/
private lemma weightedSum_rpow_pos
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    (r : ℝ) :
    0 < ∑ i ∈ s, w i * z i ^ r := by
  obtain ⟨i₀, hi₀, hwi₀⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra h; push_neg at h
    linarith [Finset.sum_eq_zero (fun i hi => le_antisymm (h i hi) (hw i hi))]
  exact lt_of_lt_of_le
    (mul_pos hwi₀ (rpow_pos_of_pos (hz i₀ hi₀) r))
    (Finset.single_le_sum
      (fun i hi => mul_nonneg (hw i hi) (rpow_nonneg (le_of_lt (hz i hi)) r)) hi₀)

/-- The weighted geometric mean GM(z,w) > 0 when all zᵢ > 0. -/
private lemma weightedGeomMean_pos (hz : ∀ i ∈ s, 0 < z i) :
    0 < weightedGeomMean s w z :=
  Finset.prod_pos (fun i hi => rpow_pos_of_pos (hz i hi) (w i))

/-- Helper: (∏ i ∈ s, f i) ^ r = ∏ i ∈ s, f i ^ r for nonneg f i. Proved by induction. -/
private lemma finset_prod_rpow (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i ∈ s, f i) ^ r = ∏ i ∈ s, f i ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
    rw [Finset.prod_insert ha,
        Real.mul_rpow (hf a (Finset.mem_insert_self a s'))
          (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        Finset.prod_insert ha,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Algebraic identity: (∏ z i ^ w i) ^ r = ∏ (z i ^ r) ^ w i.
    Both sides equal ∏ z i ^ (r * w i). -/
private lemma prod_rpow_comm
    (hz : ∀ i ∈ s, 0 ≤ z i) (r : ℝ) :
    (∏ i ∈ s, z i ^ w i) ^ r = ∏ i ∈ s, (z i ^ r) ^ w i := by
  rw [finset_prod_rpow s (fun i => z i ^ w i) (fun i hi => rpow_nonneg (hz i hi) (w i)) r]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Real.rpow_mul (hz i hi), ← Real.rpow_mul (hz i hi)]
  congr 1; ring

-- ============================================================
-- §2. KEY INEQUALITY: GM^r ≤ ∑ wᵢ zᵢ^r
-- ============================================================

/-- **Core inequality**: GM(z,w)^r ≤ ∑ wᵢ zᵢ^r for all r ∈ ℝ.

    Proof: AM-GM (geom_mean_le_arith_mean_weighted) applied to pᵢ = zᵢ^r gives:
      ∏ (zᵢ^r)^wᵢ ≤ ∑ wᵢ zᵢ^r.
    The LHS equals GM^r by `prod_rpow_comm`. -/
private lemma geomMean_rpow_le_weightedSum_rpow
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    (r : ℝ) :
    (weightedGeomMean s w z) ^ r ≤ ∑ i ∈ s, w i * z i ^ r := by
  have amgm := Real.geom_mean_le_arith_mean_weighted s w (fun i => z i ^ r) hw hw'
    (fun i hi => rpow_nonneg (le_of_lt (hz i hi)) r)
  simp only [weightedGeomMean]
  rw [prod_rpow_comm s w z (fun i hi => le_of_lt (hz i hi)) r]
  exact amgm

-- ============================================================
-- §3. GM ≤ M_r FOR r > 0
-- ============================================================

/-- **GM ≤ M_r for any r > 0**: Extends `geom_mean_le_power_mean_of_one_le` to all r > 0.

    Proof: GM = (GM^r)^(1/r) ≤ (∑ wᵢ zᵢ^r)^(1/r) = M_r.
    Uses `geomMean_rpow_le_weightedSum_rpow` and monotonicity of x ↦ x^(1/r) for r > 0. -/
theorem geom_mean_le_power_mean_pos
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hr : 0 < r) (hrne : r ≠ 0) :
    weightedGeomMean s w z ≤ weightedPowerMean s w z r hrne := by
  have hGM_pos := weightedGeomMean_pos s w z hz
  have hbound := geomMean_rpow_le_weightedSum_rpow s w z hw hw' hz r
  simp only [weightedPowerMean]
  -- GM = (GM^r)^(1/r) since r * (1/r) = 1
  conv_lhs =>
    rw [show weightedGeomMean s w z =
          (weightedGeomMean s w z ^ r) ^ (1 / r) from by
      rw [← Real.rpow_mul (le_of_lt hGM_pos), mul_one_div_cancel hrne, Real.rpow_one]]
  -- (GM^r)^(1/r) ≤ (∑ wᵢ zᵢ^r)^(1/r) since 1/r > 0
  exact Real.rpow_le_rpow (rpow_nonneg (le_of_lt hGM_pos) r) hbound
    (le_of_lt (div_pos one_pos hr))

-- ============================================================
-- §4. M_r ≤ GM FOR r < 0
-- ============================================================

/-- **M_r ≤ GM for r < 0**: The power mean of negative order is at most the geometric mean.

    Proof: From GM^r ≤ ∑ wᵢ zᵢ^r. Since 1/r < 0, raising to 1/r reverses inequality:
    M_r = (∑ wᵢ zᵢ^r)^(1/r) = ((∑ wᵢ zᵢ^r)^(-(1/r)))⁻¹
        ≤ ((GM^r)^(-(1/r)))⁻¹
        = (GM^{-1})⁻¹ = GM. -/
theorem power_mean_le_geom_mean_neg
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hr : r < 0) (hrne : r ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedGeomMean s w z := by
  have hGM_pos := weightedGeomMean_pos s w z hz
  have hbound := geomMean_rpow_le_weightedSum_rpow s w z hw hw' hz r
  have hSum_pos := weightedSum_rpow_pos s w z hw hw' hz r
  have hGMr_pos := rpow_pos_of_pos hGM_pos r
  have h_neg_r : 0 < -(1 / r) := neg_pos.mpr (div_neg_of_pos_of_neg one_pos hr)
  simp only [weightedPowerMean]
  -- GM = ((GM^r)^(-(1/r)))⁻¹
  have hGM_eq : weightedGeomMean s w z = ((weightedGeomMean s w z ^ r) ^ (-(1 / r)))⁻¹ := by
    have h : (weightedGeomMean s w z ^ r) ^ (-(1 / r)) = (weightedGeomMean s w z)⁻¹ := by
      rw [← Real.rpow_mul (le_of_lt hGM_pos)]
      rw [show r * -(1 / r) = -1 from by field_simp]
      rw [Real.rpow_neg (le_of_lt hGM_pos), Real.rpow_one]
    rw [h, inv_inv]
  rw [hGM_eq]
  -- Convert M_r = (∑)^(1/r) to ((∑)^(-(1/r)))⁻¹ using rpow_neg
  rw [show (∑ i ∈ s, w i * z i ^ r) ^ (1 / r) =
      ((∑ i ∈ s, w i * z i ^ r) ^ (-(1 / r)))⁻¹ from by
    rw [← Real.rpow_neg (le_of_lt hSum_pos), neg_neg]]
  -- Goal: ((∑)^(-(1/r)))⁻¹ ≤ ((GM^r)^(-(1/r)))⁻¹
  -- A = (GM^r)^(-(1/r)), B = (∑)^(-(1/r)). Need B⁻¹ ≤ A⁻¹ from A ≤ B.
  set A := (weightedGeomMean s w z ^ r) ^ (-(1 / r)) with hA_def
  set B := (∑ i ∈ s, w i * z i ^ r) ^ (-(1 / r)) with hB_def
  have hA_pos : (0 : ℝ) < A := by simp [hA_def]; exact rpow_pos_of_pos hGMr_pos _
  have hB_pos : (0 : ℝ) < B := by simp [hB_def]; exact rpow_pos_of_pos hSum_pos _
  have hAB : A ≤ B := by
    simp only [hA_def, hB_def]
    exact Real.rpow_le_rpow hGMr_pos.le hbound h_neg_r.le
  have hA_ne : A ≠ 0 := ne_of_gt hA_pos
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  -- Prove B⁻¹ ≤ A⁻¹ algebraically
  have key : (1 : ℝ) ≤ A⁻¹ * B := by
    calc (1 : ℝ) = A * A⁻¹ := (mul_inv_cancel₀ hA_ne).symm
      _ ≤ B * A⁻¹ := by exact mul_le_mul_of_nonneg_right hAB (inv_nonneg.mpr hA_pos.le)
      _ = A⁻¹ * B := mul_comm _ _
  have step : (1 : ℝ) * B⁻¹ ≤ A⁻¹ * B * B⁻¹ :=
    mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hB_pos.le)
  simp only [one_mul, mul_assoc, mul_inv_cancel₀ hB_ne, mul_one] at step
  exact step

-- ============================================================
-- §5. MAIN THEOREM: CROSSING ZERO MONOTONICITY
-- ============================================================

/-- **Crossing-zero monotonicity**: M_r ≤ M_s for r < 0 < s.

    Proof: M_r ≤ GM ≤ M_s (combining `power_mean_le_geom_mean_neg` and
    `geom_mean_le_power_mean_pos`). This completes the full power mean chain:

      HM = M_{-1} ≤ ... ≤ M_{r} ≤ GM = M_0 ≤ M_s ≤ ... ≤ AM = M_1 ≤ M_2 ≤ ...

    Combined with same-sign cases from AmgmInequalityOQ03, M_r is monotone for all r ≠ 0. -/
theorem power_mean_monotone_crossing_zero
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : r < 0) (ht : 0 < t)
    (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedPowerMean s w z t htne :=
  le_trans
    (power_mean_le_geom_mean_neg s w z hw hw' hz hr hrne)
    (geom_mean_le_power_mean_pos s w z hw hw' hz ht htne)

/-- **Consequence**: HM(z,w) ≤ GM(z,w) ≤ AM(z,w) via power means.
    This is a special case at r=-1, s=1 of crossing-zero monotonicity. -/
theorem hm_le_gm_le_am_via_power_means
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z (-1) (by norm_num) ≤ weightedGeomMean s w z ∧
    weightedGeomMean s w z ≤ weightedPowerMean s w z 1 (by norm_num) := by
  constructor
  · exact power_mean_le_geom_mean_neg s w z hw hw' hz (by norm_num) (by norm_num)
  · exact geom_mean_le_power_mean_pos s w z hw hw' hz (by norm_num) (by norm_num)

end PowerMeanCrossZero
