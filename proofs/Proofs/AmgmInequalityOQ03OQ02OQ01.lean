/-
# Power Means: M_r ≤ M_s for all r < 0 < s (Crossing-Zero Case)

## Open Question: amgm-inequality-oq-03-oq-02-oq-01

The power mean inequality M_r ≤ M_s holds for all r ≤ s. The same-sign cases
were proved in AmgmInequalityOQ03.lean:

- `power_mean_monotone_pos`: M_r ≤ M_s for 0 < r ≤ s (via Jensen)
- `power_mean_monotone_neg`: M_r ≤ M_s for r ≤ s < 0 (via dual argument)

The missing case is the **crossing-zero case**: r < 0 < s.

## Proof Strategy

The geometric mean GM = ∏ zᵢ^wᵢ acts as intermediary:

1. **GM ≤ M_s for s > 0**: Apply AM-GM to inputs aᵢ = zᵢ^s.
   - AM-GM: ∏ (zᵢ^s)^wᵢ ≤ ∑ wᵢ zᵢ^s
   - LHS = ∏ zᵢ^(s·wᵢ) = (∏ zᵢ^wᵢ)^s = GM^s
   - So GM^s ≤ ∑ wᵢ zᵢ^s; raise to 1/s: GM ≤ M_s.

2. **M_r ≤ GM for r < 0**: Via the dual identity M_r(z) = M_{-r}(z⁻¹)⁻¹.
   - GM(z) · GM(z⁻¹) = 1.
   - GM(z⁻¹) ≤ M_{-r}(z⁻¹) by (1) since -r > 0.
   - So 1 = GM(z) · GM(z⁻¹) ≤ GM(z) · M_{-r}(z⁻¹), giving M_{-r}(z⁻¹)⁻¹ ≤ GM(z).

3. Transitivity: M_r ≤ GM ≤ M_s.
-/

import Proofs.AmgmInequalityOQ03

open Finset Real

namespace AmgmInequalityOQ03OQ02OQ01

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-! ## Helper: (∏ fᵢ)^q = ∏ fᵢ^q for positive fᵢ -/

/-- For positive inputs, the q-th power distributes over finite products. -/
private lemma finset_prod_rpow_pos : ∀ (t : Finset ι) (f : ι → ℝ),
    (∀ i ∈ t, 0 < f i) → ∀ (q : ℝ), (∏ i ∈ t, f i) ^ q = ∏ i ∈ t, f i ^ q := by
  intro t
  induction t using Finset.cons_induction with
  | empty => intros; simp
  | cons a s ha ih =>
    intro f hf q
    have hfa : 0 < f a := hf a (Finset.mem_cons_self a s)
    have hfs : ∀ i ∈ s, 0 < f i := fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
    rw [Finset.prod_cons, Finset.prod_cons,
        Real.mul_rpow (le_of_lt hfa)
          (Finset.prod_nonneg fun i hi => le_of_lt (hfs i hi))]
    congr 1
    exact ih f hfs q

/-! ## Helper: weighted sum is positive -/

private lemma wsum_pos (t : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ t, 0 ≤ v i) (hv' : ∑ i ∈ t, v i = 1)
    (f : ι → ℝ) (hf : ∀ i ∈ t, 0 < f i) {q : ℝ} :
    0 < ∑ i ∈ t, v i * f i ^ q := by
  obtain ⟨i₀, hi₀, hvi₀⟩ : ∃ i ∈ t, 0 < v i := by
    by_contra h; push_neg at h
    have := Finset.sum_eq_zero (fun i hi => le_antisymm (h i hi) (hv i hi))
    linarith
  exact lt_of_lt_of_le
    (mul_pos hvi₀ (Real.rpow_pos_of_pos (hf i₀ hi₀) q))
    (Finset.single_le_sum
      (fun i hi => mul_nonneg (hv i hi) (Real.rpow_nonneg (le_of_lt (hf i hi)) q)) hi₀)

/-! ## Step 1: GM ≤ M_s for s > 0 -/

/-- **GM ≤ M_s for any s > 0**.

Proof: Apply AM-GM to aᵢ = zᵢ^s. Then GM^s = ∏ (zᵢ^s)^wᵢ ≤ ∑ wᵢ zᵢ^s.
Raise to 1/s to get GM ≤ M_s. -/
theorem geom_mean_le_power_mean_pos
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {p : ℝ} (hp : 0 < p) (hpne : p ≠ 0) :
    weightedGeomMean s w z ≤ weightedPowerMean s w z p hpne := by
  simp only [weightedPowerMean, weightedGeomMean]
  have hz_nn : ∀ i ∈ s, 0 ≤ z i := fun i hi => le_of_lt (hz i hi)
  -- AM-GM applied to aᵢ = zᵢ^p: ∏ (zᵢ^p)^wᵢ ≤ ∑ wᵢ (zᵢ^p)
  have amgm : ∏ i ∈ s, (z i ^ p) ^ w i ≤ ∑ i ∈ s, w i * z i ^ p :=
    Real.geom_mean_le_arith_mean_weighted s w (fun i => z i ^ p) hw hw'
      (fun i hi => Real.rpow_nonneg (hz_nn i hi) p)
  -- (zᵢ^p)^wᵢ = (zᵢ^wᵢ)^p for each i (by rpow_mul commutativity)
  have step1 : ∀ i ∈ s, (z i ^ p) ^ w i = (z i ^ w i) ^ p := fun i hi => by
    rw [← Real.rpow_mul (hz_nn i hi) p (w i),
        mul_comm p (w i),
        Real.rpow_mul (hz_nn i hi) (w i) p]
  rw [Finset.prod_congr rfl step1] at amgm
  -- ∏ (zᵢ^wᵢ)^p = (∏ zᵢ^wᵢ)^p (by finset_prod_rpow_pos)
  rw [← finset_prod_rpow_pos s (fun i => z i ^ w i)
      (fun i hi => Real.rpow_pos_of_pos (hz i hi) (w i)) p] at amgm
  -- amgm: (∏ zᵢ^wᵢ)^p ≤ ∑ wᵢ zᵢ^p; raise to 1/p
  have hGM_nn : 0 ≤ ∏ i ∈ s, z i ^ w i :=
    Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hz_nn i hi) _
  calc ∏ i ∈ s, z i ^ w i
      = ((∏ i ∈ s, z i ^ w i) ^ p) ^ (1 / p) := by
          rw [← Real.rpow_mul hGM_nn, one_div, mul_inv_cancel₀ hpne, Real.rpow_one]
    _ ≤ (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hGM_nn _) amgm (by positivity)

/-! ## Step 2: M_r ≤ GM for r < 0 -/

/-- **GM(z) · GM(z⁻¹) = 1** for positive inputs. -/
lemma geom_mean_mul_inv_eq_one
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedGeomMean s w z * weightedGeomMean s w (fun i => (z i)⁻¹) = 1 := by
  simp only [weightedGeomMean, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  rw [← Real.mul_rpow (le_of_lt (hz i hi)) (inv_nonneg.mpr (le_of_lt (hz i hi))),
      mul_inv_cancel₀ (ne_of_gt (hz i hi)), Real.one_rpow]

/-- **M_r ≤ GM for r < 0** (via dual argument). -/
theorem power_mean_le_geom_mean_neg
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hr : r < 0) (hrne : r ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedGeomMean s w z := by
  have hnr_pos : 0 < -r := neg_pos.mpr hr
  have hnr_ne : -r ≠ 0 := ne_of_gt hnr_pos
  have hzinv : ∀ i ∈ s, 0 < (fun i => (z i)⁻¹) i := fun i hi => inv_pos.mpr (hz i hi)
  -- GM(z⁻¹) ≤ M_{-r}(z⁻¹) since -r > 0
  have h_gm_le : weightedGeomMean s w (fun i => (z i)⁻¹) ≤
      weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hnr_ne :=
    geom_mean_le_power_mean_pos s w (fun i => (z i)⁻¹) hw hw' hzinv hnr_pos hnr_ne
  -- M_{-r}(z⁻¹) > 0
  have hM_pos : 0 < weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hnr_ne := by
    simp only [weightedPowerMean]
    exact Real.rpow_pos_of_pos (wsum_pos s w hw hw' (fun i => (z i)⁻¹) hzinv) _
  -- GM(z) > 0
  have hGM_pos : 0 < weightedGeomMean s w z :=
    Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hz i hi) (w i)
  -- GM(z) · GM(z⁻¹) = 1
  have hprod : weightedGeomMean s w z * weightedGeomMean s w (fun i => (z i)⁻¹) = 1 :=
    geom_mean_mul_inv_eq_one s w z hw hz
  -- M_r(z) = M_{-r}(z⁻¹)⁻¹
  rw [power_mean_neg_inv s w z hw hz hrne]
  -- 1 = GM · GM(z⁻¹) ≤ GM · M_{-r}(z⁻¹), so M_{-r}(z⁻¹)⁻¹ ≤ GM
  have key : 1 ≤ weightedGeomMean s w z *
      weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hnr_ne :=
    hprod.symm ▸ mul_le_mul_of_nonneg_left h_gm_le (le_of_lt hGM_pos)
  have step := mul_le_mul_of_nonneg_right key (inv_nonneg.mpr (le_of_lt hM_pos))
  rwa [one_mul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hM_pos), mul_one] at step

/-! ## Main Result -/

/-- **Power Mean Monotonicity: Crossing-Zero Case** (OQ-03-OQ-02-OQ-01).

For r < 0 < s: M_r ≤ GM ≤ M_s. Combined with the same-sign cases from
AmgmInequalityOQ03.lean, this completes full power mean monotonicity for all r ≤ s. -/
theorem power_mean_monotone_mixed
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : r < 0) (ht : 0 < t)
    (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedPowerMean s w z t htne :=
  (power_mean_le_geom_mean_neg s w z hw hw' hz hr hrne).trans
    (geom_mean_le_power_mean_pos s w z hw hw' hz ht htne)

/-- **Full Power Mean Monotonicity** for all r ≤ s (r ≠ 0, s ≠ 0). -/
theorem power_mean_monotone_all
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hrt : r ≤ t)
    (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedPowerMean s w z t htne := by
  rcases le_or_gt 0 r with hr_nn | hr_neg
  · exact power_mean_monotone_pos s w z hw hw' hz
      (lt_of_le_of_ne hr_nn (Ne.symm hrne)) hrt hrne htne
  · rcases le_or_gt 0 t with ht_nn | ht_neg
    · exact power_mean_monotone_mixed s w z hw hw' hz hr_neg
        (lt_of_le_of_ne ht_nn (Ne.symm htne)) hrne htne
    · exact power_mean_monotone_neg s w z hw hw' hz hrt ht_neg hrne htne

end AmgmInequalityOQ03OQ02OQ01
