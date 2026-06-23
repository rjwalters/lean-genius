/-
  Equality case of the crossing-zero power-mean chain
  Open Question: amgm-inequality-oq-03-oq-02-oq-01-oq-02

  The crossing-zero file `PowerMeanCrossZeroOQ` proves the *inequalities*

      M_r(z,w) ≤ GM(z,w) ≤ M_s(z,w)        for  r < 0 < s,

  where GM is the weighted geometric mean and M_p the weighted power mean of
  order p. Those bounds are all non-strict. This file supplies the **sharp
  converse**: it characterizes exactly when equality holds, and upgrades the
  bounds to strict inequalities off the diagonal.

  ## Headline results

  * `power_mean_eq_geom_mean_iff` — for **every** exponent `r ≠ 0` (positive or
    negative!), `M_r = GM ↔ all data equal`. The equality locus is the *same*
    for both signs of `r`, even though the inequality flips direction across
    zero (GM ≤ M_r for r > 0, M_r ≤ GM for r < 0). This sign-independent
    unification is the main observation.
  * `power_mean_crossing_zero_eq_iff` — for `r < 0 < t`,
    `M_r = M_t ↔ all data equal`, the sharp converse to
    `power_mean_monotone_crossing_zero`.
  * `power_mean_lt_geom_mean_neg_of_ne`, `geom_mean_lt_power_mean_pos_of_ne`,
    `power_mean_crossing_zero_lt_of_ne` — the strict forms for non-constant data.
  * `hm_lt_gm_lt_am_of_ne`, `hm_eq_gm_iff` — the classical HM < GM < AM corner.

  ## Engine

  The single fact behind all of this is the equality case of weighted AM–GM,
  `weighted_amgm_eq_iff` (root `JensenInequalityOQ01`), applied to the *powered*
  data `uᵢ = zᵢ^r`:

      GM^r = ∑ wᵢ zᵢ^r   ↔   ∀ j k, zⱼ^r = zₖ^r   ↔   ∀ j k, zⱼ = zₖ,

  the last step by injectivity of `x ↦ x^r` on the positives (`r ≠ 0`). Raising
  to the (bijective) power `1/r` then converts `GM^r = ∑ wᵢ zᵢ^r` to `GM = M_r`,
  *independently of the sign of `r`*. No limit arguments are used.
-/

import Proofs.AmgmInequalityOQ03
import Proofs.JensenInequalityOQ01
import Proofs.PowerMeanCrossZeroOQ
import Mathlib.Tactic

open Real Finset

namespace PowerMeanCrossZeroEq

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

-- ============================================================
-- §1. POSITIVITY AND ALGEBRAIC HELPERS
-- ============================================================

/-- The weighted sum `∑ wᵢ zᵢ^r > 0` when the weights sum to `1` and all `zᵢ > 0`. -/
private lemma weightedSum_rpow_pos
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) (r : ℝ) :
    0 < ∑ i ∈ s, w i * z i ^ r := by
  obtain ⟨i₀, hi₀, hwi₀⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra h; push_neg at h
    linarith [Finset.sum_eq_zero (fun i hi => le_antisymm (h i hi) (hw i hi))]
  exact lt_of_lt_of_le
    (mul_pos hwi₀ (Real.rpow_pos_of_pos (hz i₀ hi₀) r))
    (Finset.single_le_sum
      (fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hz i hi).le r)) hi₀)

/-- The weighted geometric mean `GM(z,w) > 0` when all `zᵢ > 0`. -/
private lemma weightedGeomMean_pos (hz : ∀ i ∈ s, 0 < z i) :
    0 < weightedGeomMean s w z :=
  Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (hz i hi) (w i))

/-- `(∏ fᵢ)^r = ∏ fᵢ^r` for nonnegative `f` (induction on the index set). -/
private lemma finset_prod_rpow (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
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

/-- `GM^r = ∏ (zᵢ^r)^wᵢ`: both sides equal `∏ zᵢ^(r·wᵢ)`. -/
private lemma geomMean_rpow_eq (hz : ∀ i ∈ s, 0 ≤ z i) (r : ℝ) :
    (weightedGeomMean s w z) ^ r = ∏ i ∈ s, (z i ^ r) ^ w i := by
  simp only [weightedGeomMean]
  rw [finset_prod_rpow s (fun i => z i ^ w i) (fun i hi => Real.rpow_nonneg (hz i hi) (w i)) r]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Real.rpow_mul (hz i hi), ← Real.rpow_mul (hz i hi)]
  congr 1; ring

-- ============================================================
-- §2. CORE EQUALITY LEMMA:  GM^r = ∑ wᵢ zᵢ^r  ↔  constant
-- ============================================================

/-- **Equality case of the core inequality.** For any `r ≠ 0`, strictly positive
weights summing to `1`, and strictly positive data,

    GM^r = ∑ wᵢ zᵢ^r   ↔   all the data are equal.

This is `weighted_amgm_eq_iff` applied to the powered data `zᵢ^r`, with the
right-hand equalities `zⱼ^r = zₖ^r` collapsed to `zⱼ = zₖ` by injectivity of
`x ↦ x^r` on the positives. -/
theorem geomMean_rpow_eq_weightedSum_rpow_iff
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hrne : r ≠ 0) :
    (weightedGeomMean s w z) ^ r = ∑ i ∈ s, w i * z i ^ r
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  have key := weighted_amgm_eq_iff (s := s) (w := w) (z := fun i => z i ^ r)
    hw hw' (fun i hi => Real.rpow_nonneg (hz i hi).le r)
  simp only [] at key
  rw [geomMean_rpow_eq s w z (fun i hi => (hz i hi).le) r, key]
  constructor
  · intro h j hj k hk
    exact (Real.rpow_left_inj (hz j hj).le (hz k hk).le hrne).mp (h j hj k hk)
  · intro h j hj k hk
    rw [h j hj k hk]

-- ============================================================
-- §3. THE SIGN-INDEPENDENT EQUALITY CASE:  M_r = GM  ↔  constant
-- ============================================================

/-- **The geometric mean equals the power mean of order `r` iff the data is
constant — for every `r ≠ 0`.**

Although the *inequality* between `GM` and `M_r` reverses across zero
(`GM ≤ M_r` for `r > 0`, `M_r ≤ GM` for `r < 0`), the *equality locus* is
identical and sign-independent: in both cases `M_r = GM` exactly when all the
`zᵢ` coincide. -/
theorem power_mean_eq_geom_mean_iff
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hrne : r ≠ 0) :
    weightedPowerMean s w z r hrne = weightedGeomMean s w z
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  have hwnn : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  have hSum := weightedSum_rpow_pos s w z hwnn hw' hz r
  have hGM := weightedGeomMean_pos s w z hz
  have hMr_pos : 0 < weightedPowerMean s w z r hrne := by
    simp only [weightedPowerMean]; exact Real.rpow_pos_of_pos hSum _
  -- M_r raised back to the r-th power recovers the underlying weighted sum.
  have hMr_eq : weightedPowerMean s w z r hrne ^ r = ∑ i ∈ s, w i * z i ^ r := by
    simp only [weightedPowerMean]
    rw [← Real.rpow_mul hSum.le, one_div_mul_cancel hrne, Real.rpow_one]
  rw [← geomMean_rpow_eq_weightedSum_rpow_iff s w z hw hw' hz hrne,
      ← Real.rpow_left_inj hMr_pos.le hGM.le hrne, hMr_eq]
  exact eq_comm

-- ============================================================
-- §4. CROSSING-ZERO EQUALITY AND STRICTNESS
-- ============================================================

/-- **Sharp converse to crossing-zero monotonicity.** For `r < 0 < t`,

    M_r = M_t   ↔   all the data are equal.

The forward direction squeezes `M_r ≤ GM ≤ M_t` against the assumed equality to
force `M_r = GM`, then applies `power_mean_eq_geom_mean_iff`. -/
theorem power_mean_crossing_zero_eq_iff
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : r < 0) (ht : 0 < t) (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne = weightedPowerMean s w z t htne
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  have hwnn : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  constructor
  · intro h
    have h1 := PowerMeanCrossZero.power_mean_le_geom_mean_neg s w z hwnn hw' hz hr hrne
    have h2 := PowerMeanCrossZero.geom_mean_le_power_mean_pos s w z hwnn hw' hz ht htne
    have hge : weightedGeomMean s w z ≤ weightedPowerMean s w z r hrne := by
      rw [h]; exact h2
    exact (power_mean_eq_geom_mean_iff s w z hw hw' hz hrne).mp (le_antisymm h1 hge)
  · intro h
    rw [(power_mean_eq_geom_mean_iff s w z hw hw' hz hrne).mpr h,
        (power_mean_eq_geom_mean_iff s w z hw hw' hz htne).mpr h]

/-- **Strict lower bound for negative order.** If two of the values differ then
`M_r < GM` for `r < 0`. -/
theorem power_mean_lt_geom_mean_neg_of_ne
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hr : r < 0) (hrne : r ≠ 0)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    weightedPowerMean s w z r hrne < weightedGeomMean s w z := by
  have hwnn : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  refine lt_of_le_of_ne
    (PowerMeanCrossZero.power_mean_le_geom_mean_neg s w z hwnn hw' hz hr hrne) ?_
  intro hEq
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  exact hjk ((power_mean_eq_geom_mean_iff s w z hw hw' hz hrne).mp hEq j hj k hk)

/-- **Strict upper bound for positive order.** If two of the values differ then
`GM < M_t` for `t > 0`. -/
theorem geom_mean_lt_power_mean_pos_of_ne
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {t : ℝ} (ht : 0 < t) (htne : t ≠ 0)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    weightedGeomMean s w z < weightedPowerMean s w z t htne := by
  have hwnn : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  refine lt_of_le_of_ne
    (PowerMeanCrossZero.geom_mean_le_power_mean_pos s w z hwnn hw' hz ht htne) ?_
  intro hEq
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  exact hjk ((power_mean_eq_geom_mean_iff s w z hw hw' hz htne).mp hEq.symm j hj k hk)

/-- **Strict crossing-zero inequality.** For `r < 0 < t` and non-constant data,
`M_r < M_t`. -/
theorem power_mean_crossing_zero_lt_of_ne
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : r < 0) (ht : 0 < t) (hrne : r ≠ 0) (htne : t ≠ 0)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    weightedPowerMean s w z r hrne < weightedPowerMean s w z t htne := by
  have hwnn : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  refine lt_of_le_of_ne
    (PowerMeanCrossZero.power_mean_monotone_crossing_zero s w z hwnn hw' hz hr ht hrne htne) ?_
  intro hEq
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  exact hjk ((power_mean_crossing_zero_eq_iff s w z hw hw' hz hr ht hrne htne).mp hEq j hj k hk)

-- ============================================================
-- §5. THE CLASSICAL HM ≤ GM ≤ AM CORNER (SHARP)
-- ============================================================

/-- **HM = GM iff the data is constant.** The `r = -1` specialization of
`power_mean_eq_geom_mean_iff`. -/
theorem hm_eq_gm_iff
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z (-1) (by norm_num) = weightedGeomMean s w z
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k :=
  power_mean_eq_geom_mean_iff s w z hw hw' hz (by norm_num)

/-- **Strict HM < GM < AM for non-constant data.** Combines the two strict
crossing-zero bounds at `r = -1` and `t = 1`. -/
theorem hm_lt_gm_lt_am_of_ne
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    weightedPowerMean s w z (-1) (by norm_num) < weightedGeomMean s w z ∧
    weightedGeomMean s w z < weightedPowerMean s w z 1 (by norm_num) :=
  ⟨power_mean_lt_geom_mean_neg_of_ne s w z hw hw' hz (by norm_num) (by norm_num) hne,
   geom_mean_lt_power_mean_pos_of_ne s w z hw hw' hz (by norm_num) (by norm_num) hne⟩

end PowerMeanCrossZeroEq
