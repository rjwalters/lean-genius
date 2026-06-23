/-
# Extended Power Mean Monotonicity: Unified Single Theorem

## Open Question: amgm-inequality-oq-03-oq-02-oq-01-oq-01

**Unify the three power mean monotonicity cases into a single theorem.**

The parent files prove three separate monotonicity results:
1. `power_mean_monotone_pos`: M_r ≤ M_s for 0 < r ≤ s  (AmgmInequalityOQ03.lean)
2. `power_mean_monotone_neg`: M_r ≤ M_s for r ≤ s < 0  (AmgmInequalityOQ03.lean)
3. `power_mean_monotone_mixed`: M_r ≤ M_s for r < 0 < s  (AmgmInequalityOQ03OQ02OQ01.lean)

The `power_mean_monotone_all` theorem combines these three for r ≠ 0, s ≠ 0.
This file extends to **ALL r ≤ s** by including the boundary cases r = 0 or s = 0,
where M_0 = GM = ∏ zᵢ^{wᵢ} (the geometric mean as the r → 0 limit).

## Main Result

We define the **extended power mean** M_r for ALL r ∈ ℝ:

  extWeightedPowerMean(r) = GM(z, w)        if r = 0
                           = M_r(z, w)       if r ≠ 0

Then `extWeightedPowerMean_monotone` gives a single theorem:

  ∀ r ≤ s, extWeightedPowerMean(r) ≤ extWeightedPowerMean(s)

This handles all four sub-cases uniformly:
- r = 0, s = 0: trivial (equality)
- r = 0, s > 0: GM ≤ M_s (from `geom_mean_le_power_mean_pos`)
- r < 0, s = 0: M_r ≤ GM (from `power_mean_le_geom_mean_neg`)
- r ≠ 0, s ≠ 0: `power_mean_monotone_all`

## References

- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). Inequalities. Cambridge.
- Parent: AmgmInequalityOQ03OQ02OQ01.lean (crossing-zero case + power_mean_monotone_all)
-/

import Proofs.AmgmInequalityOQ03OQ02OQ01

open AmgmInequalityOQ03OQ02OQ01

namespace AmgmInequalityOQ03OQ02OQ01OQ01

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-! ## Extended Power Mean Definition -/

/-- The **extended power mean** M_r for ALL r ∈ ℝ, including r = 0.

M_0 is defined as the geometric mean GM = ∏ zᵢ^{wᵢ}, which is the
limit of the power mean M_r as r → 0 (by continuity). -/
noncomputable def extWeightedPowerMean (r : ℝ) : ℝ :=
  if h : r = 0 then weightedGeomMean s w z else weightedPowerMean s w z r h

/-- At r = 0, the extended power mean is the geometric mean. -/
@[simp]
theorem extWeightedPowerMean_zero :
    extWeightedPowerMean s w z 0 = weightedGeomMean s w z := dif_pos rfl

/-- For r ≠ 0, the extended power mean equals the usual power mean. -/
theorem extWeightedPowerMean_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    extWeightedPowerMean s w z r = weightedPowerMean s w z r hr := dif_neg hr

/-! ## The Unified Monotonicity Theorem -/

/-- **Extended Power Mean Monotonicity** (the unified single theorem).

For any r ≤ s (no restriction on sign or zero),

  extWeightedPowerMean(r) ≤ extWeightedPowerMean(s).

This is the complete power mean monotonicity, unifying all three cases:
1. Both positive (r, s > 0): via Jensen's inequality
2. Both negative (r, s < 0): via dual inversion argument
3. Crossing zero (r < 0 < s): via transitivity through the geometric mean

The boundary cases r = 0 or s = 0 (geometric mean) are included through
the extended definition and the bounds `GM ≤ M_s` (s > 0) and `M_r ≤ GM` (r < 0). -/
theorem extWeightedPowerMean_monotone
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hrt : r ≤ t) :
    extWeightedPowerMean s w z r ≤ extWeightedPowerMean s w z t := by
  unfold extWeightedPowerMean
  rcases eq_or_ne r 0 with hr | hr
  · rcases eq_or_ne t 0 with ht | ht
    · -- Case r = 0, t = 0: trivial (both are GM)
      rw [dif_pos hr, dif_pos ht]
    · -- Case r = 0, t ≠ 0: t > 0 (from 0 = r ≤ t, t ≠ 0), so GM ≤ M_t
      have ht_pos : 0 < t := lt_of_le_of_ne (hr ▸ hrt) (Ne.symm ht)
      rw [dif_pos hr, dif_neg ht]
      exact geom_mean_le_power_mean_pos s w z hw hw' hz ht_pos ht
  · rcases eq_or_ne t 0 with ht | ht
    · -- Case r ≠ 0, t = 0: r < 0 (from r ≤ 0 = t, r ≠ 0), so M_r ≤ GM
      have hr_neg : r < 0 := lt_of_le_of_ne (ht ▸ hrt) hr
      rw [dif_neg hr, dif_pos ht]
      exact power_mean_le_geom_mean_neg s w z hw hw' hz hr_neg hr
    · -- Case r ≠ 0, t ≠ 0: apply power_mean_monotone_all
      rw [dif_neg hr, dif_neg ht]
      exact power_mean_monotone_all s w z hw hw' hz hrt hr ht

/-! ## Corollaries -/

/-- **HM ≤ GM ≤ AM** as a corollary of extended monotonicity.

The classical inequalities HM ≤ GM ≤ AM follow immediately:
- HM = M_{-1}, GM = M_0, AM = M_1
- Since -1 ≤ 0 ≤ 1, extended monotonicity gives HM ≤ GM ≤ AM. -/
theorem hm_le_gm_le_am
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z (-1) (by norm_num) ≤ weightedGeomMean s w z ∧
    weightedGeomMean s w z ≤ weightedPowerMean s w z 1 (by norm_num) := by
  constructor
  · -- HM ≤ GM: M_{-1} ≤ M_0
    have h := extWeightedPowerMean_monotone s w z hw hw' hz (show (-1 : ℝ) ≤ 0 by norm_num)
    rw [extWeightedPowerMean_of_ne_zero s w z (by norm_num : (-1 : ℝ) ≠ 0),
        extWeightedPowerMean_zero] at h
    exact h
  · -- GM ≤ AM: M_0 ≤ M_1
    have h := extWeightedPowerMean_monotone s w z hw hw' hz (show (0 : ℝ) ≤ 1 by norm_num)
    rw [extWeightedPowerMean_zero,
        extWeightedPowerMean_of_ne_zero s w z (by norm_num : (1 : ℝ) ≠ 0)] at h
    exact h

/-- **Monotone family**: The map r ↦ extWeightedPowerMean(r) is monotone on ℝ. -/
theorem extWeightedPowerMean_monotone_fun
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    Monotone (extWeightedPowerMean s w z) :=
  fun _ _ hrt => extWeightedPowerMean_monotone s w z hw hw' hz hrt

end AmgmInequalityOQ03OQ02OQ01OQ01
