/-
# Weighted Power Means: Interpolating Between AM and GM

## Open Question: amgm-inequality-oq-03

How do weighted power means interpolate between the arithmetic mean (AM) and
geometric mean (GM)?

The **weighted power mean** of order r for non-negative reals z₁, ..., zₙ
with weights w₁, ..., wₙ (summing to 1) is:

  M_r(z, w) = (Σ wᵢ · zᵢ^r)^(1/r)   for r ≠ 0

Key special cases:
- M₁(z, w) = Σ wᵢ · zᵢ  [the weighted arithmetic mean AM]
- M_{-1}(z, w) = (Σ wᵢ / zᵢ)^{-1}  [the weighted harmonic mean HM]
- lim_{r→0} M_r(z, w) = ∏ zᵢ^{wᵢ}  [the weighted geometric mean GM]

The **Power Mean Inequality** (monotonicity): For r ≤ s,

  M_r(z, w) ≤ M_s(z, w)

In particular:  HM ≤ GM ≤ AM  (taking r = -1, 0, 1).

## What This File Proves

1. `power_mean_one_eq_arith_mean` — M_1 equals the weighted arithmetic mean
2. `arith_mean_le_power_mean` — AM ≤ M_p for p ≥ 1 (from Mathlib Jensen)
3. `geom_mean_le_arith_mean` — GM ≤ AM (from Mathlib)
4. `geom_mean_le_power_mean_of_one_le` — GM ≤ M_p for p ≥ 1
5. `harmonic_mean_le_geom_mean_direct` — HM ≤ GM (direct proof via AM-GM on inverses)
6. `power_mean_monotone_pos` — M_r ≤ M_s for 0 < r ≤ s (proved via Jensen)
7. General monotonicity (negative r case) stated as an axiom

## Key Proof Ideas

**HM ≤ GM**: Apply AM-GM to inverse values yᵢ = zᵢ⁻¹:
  (∏ zᵢ^wᵢ)⁻¹ = ∏ (zᵢ⁻¹)^wᵢ ≤ ∑ wᵢ/zᵢ = 1/HM
So HM ≤ GM.

**M_r ≤ M_s for 0 < r ≤ s**: Apply Jensen (t ↦ t^(s/r) is convex) to inputs aᵢ = zᵢ^r:
  (Σ wᵢ zᵢ^r)^(s/r) ≤ Σ wᵢ zᵢ^s
Raise both sides to 1/s: M_r = (Σ wᵢ zᵢ^r)^(1/r) ≤ (Σ wᵢ zᵢ^s)^(1/s) = M_s.

## References

- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). Inequalities. Cambridge.
- Mathlib: `Mathlib.Analysis.MeanInequalitiesPow`
- Mathlib TODO: "generalized mean inequality with any p ≤ q, including negative numbers"
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-- The **weighted power mean** of order p (for p ≠ 0):
    M_p(z, w) = (Σ_{i∈s} wᵢ · zᵢ^p)^(1/p) -/
noncomputable def weightedPowerMean (p : ℝ) (hp : p ≠ 0) : ℝ :=
  (∑ i ∈ s, w i * z i ^ p) ^ (1 / p)

/-- The **weighted geometric mean**: GM(z, w) = ∏_{i∈s} zᵢ^{wᵢ} -/
noncomputable def weightedGeomMean : ℝ :=
  ∏ i ∈ s, z i ^ w i

/-- The **weighted arithmetic mean**: AM(z, w) = Σ_{i∈s} wᵢ · zᵢ -/
noncomputable def weightedArithMean : ℝ :=
  ∑ i ∈ s, w i * z i

/-- **M₁ = AM**: The power mean of order 1 equals the arithmetic mean. -/
theorem power_mean_one_eq_arith_mean :
    weightedPowerMean s w z 1 (by norm_num) = weightedArithMean s w z := by
  simp [weightedPowerMean, weightedArithMean, Real.rpow_one]

/-- **AM ≤ M_p for p ≥ 1** (Jensen's inequality / power mean inequality).

This is a direct consequence of Mathlib's `Real.arith_mean_le_rpow_mean`. -/
theorem arith_mean_le_power_mean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p)
    (hpne : p ≠ 0) :
    weightedArithMean s w z ≤ weightedPowerMean s w z p hpne :=
  Real.arith_mean_le_rpow_mean s w z hw hw' hz hp

/-- **GM ≤ AM** (classical AM-GM inequality from Mathlib). -/
theorem geom_mean_le_arith_mean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    weightedGeomMean s w z ≤ weightedArithMean s w z :=
  Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz

/-- **GM ≤ M_p for p ≥ 1** (transitivity through AM). -/
theorem geom_mean_le_power_mean_of_one_le
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p)
    (hpne : p ≠ 0) :
    weightedGeomMean s w z ≤ weightedPowerMean s w z p hpne :=
  (geom_mean_le_arith_mean s w z hw hw' hz).trans
    (arith_mean_le_power_mean s w z hw hw' hz hp hpne)

/-- **Jensen's inequality for power functions**.

For p ≥ 1, the function t ↦ t^p is convex, so:
  (Σ wᵢ · zᵢ)^p ≤ Σ wᵢ · zᵢ^p -/
theorem jensen_pow_ineq
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
  Real.rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp

/-- **HM ≤ GM** (direct proof via AM-GM on inverse values).

**Proof**: Apply AM-GM to yᵢ = zᵢ⁻¹:
  GM(z⁻¹) ≤ AM(z⁻¹) = ∑ wᵢ/zᵢ = 1/HM
Key step: GM(z⁻¹) = 1/GM(z), proved via GM(z⁻¹)·GM(z) = ∏ zᵢ⁻¹^wᵢ·zᵢ^wᵢ = 1.
So 1/GM ≤ 1/HM, i.e., HM ≤ GM. -/
theorem harmonic_mean_le_geom_mean_direct
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i * (z i)⁻¹)⁻¹ ≤ weightedGeomMean s w z := by
  -- GM > 0
  have hGM_pos : 0 < weightedGeomMean s w z := by
    unfold weightedGeomMean
    apply Finset.prod_pos
    intro i hi
    exact Real.rpow_pos_of_pos (hz i hi) (w i)
  -- GM(z⁻¹) · GM(z) = 1, hence GM(z⁻¹) = GM(z)⁻¹
  have hprod_one : weightedGeomMean s w (fun i => (z i)⁻¹) * weightedGeomMean s w z = 1 := by
    simp only [weightedGeomMean, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    rw [← Real.mul_rpow (inv_nonneg.mpr (le_of_lt (hz i hi))) (le_of_lt (hz i hi)),
        inv_mul_cancel₀ (ne_of_gt (hz i hi)),
        Real.one_rpow]
  have geom_inv : weightedGeomMean s w (fun i => (z i)⁻¹) = (weightedGeomMean s w z)⁻¹ := by
    apply mul_right_cancel₀ (ne_of_gt hGM_pos)
    rw [hprod_one, inv_mul_cancel₀ (ne_of_gt hGM_pos)]
  -- Apply AM-GM to z⁻¹: GM(z⁻¹) ≤ ∑ wᵢ·zᵢ⁻¹
  have hzinvnn : ∀ i ∈ s, 0 ≤ (z i)⁻¹ := fun i hi => inv_nonneg.mpr (le_of_lt (hz i hi))
  have amgm_inv : weightedGeomMean s w (fun i => (z i)⁻¹) ≤ ∑ i ∈ s, w i * (z i)⁻¹ :=
    Real.geom_mean_le_arith_mean_weighted s w (fun i => (z i)⁻¹) hw hw' hzinvnn
  -- Substitute: GM(z)⁻¹ ≤ ∑ wᵢ·zᵢ⁻¹
  rw [geom_inv] at amgm_inv
  -- AM_inv > 0 (since it's ≥ GM(z)⁻¹ > 0)
  have h_AM_pos : 0 < ∑ i ∈ s, w i * (z i)⁻¹ :=
    lt_of_lt_of_le (inv_pos.mpr hGM_pos) amgm_inv
  -- Invert: (∑ wᵢ/zᵢ)⁻¹ ≤ GM(z)
  -- Key: 1 ≤ GM * Σ, multiply both sides by Σ⁻¹ to get Σ⁻¹ ≤ GM
  have h_sum_ne : (∑ i ∈ s, w i * (z i)⁻¹) ≠ 0 := ne_of_gt h_AM_pos
  have key : 1 ≤ weightedGeomMean s w z * (∑ i ∈ s, w i * (z i)⁻¹) :=
    calc (1 : ℝ) = weightedGeomMean s w z * (weightedGeomMean s w z)⁻¹ :=
            (mul_inv_cancel₀ (ne_of_gt hGM_pos)).symm
      _ ≤ weightedGeomMean s w z * (∑ i ∈ s, w i * (z i)⁻¹) :=
            mul_le_mul_of_nonneg_left amgm_inv (le_of_lt hGM_pos)
  have step := mul_le_mul_of_nonneg_right key (inv_nonneg.mpr (le_of_lt h_AM_pos))
  rw [one_mul] at step
  rwa [mul_assoc, mul_inv_cancel₀ h_sum_ne, mul_one] at step

/-- **Power Mean Monotonicity for 0 < r ≤ s** (proved via Jensen).

For 0 < r ≤ s, the power mean M_r(z,w) ≤ M_s(z,w).

**Proof**: Let q = s/r ≥ 1. Apply Jensen to aᵢ = zᵢ^r:
  (Σ wᵢ zᵢ^r)^(s/r) ≤ Σ wᵢ (zᵢ^r)^(s/r) = Σ wᵢ zᵢ^s
Raise to 1/s: (Σ wᵢ zᵢ^r)^(1/r) ≤ (Σ wᵢ zᵢ^s)^(1/s). -/
theorem power_mean_monotone_pos
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t)
    (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedPowerMean s w z t htne := by
  simp only [weightedPowerMean]
  have ht_pos : 0 < t := lt_of_lt_of_le hr hrt
  -- q = t/r ≥ 1
  have hq : 1 ≤ t / r := by
    calc (1 : ℝ) = r * r⁻¹ := (mul_inv_cancel₀ (ne_of_gt hr)).symm
      _ ≤ t * r⁻¹ := mul_le_mul_of_nonneg_right hrt (inv_nonneg.mpr (le_of_lt hr))
      _ = t / r := by ring
  -- zᵢ^r ≥ 0
  have hzr_nn : ∀ i ∈ s, 0 ≤ (fun i => z i ^ r) i :=
    fun i hi => Real.rpow_nonneg (le_of_lt (hz i hi)) r
  -- Jensen: (Σ wᵢ (zᵢ^r))^(t/r) ≤ Σ wᵢ (zᵢ^r)^(t/r)
  have jensen : (∑ i ∈ s, w i * z i ^ r) ^ (t / r) ≤ ∑ i ∈ s, w i * (z i ^ r) ^ (t / r) :=
    Real.rpow_arith_mean_le_arith_mean_rpow s w (fun i => z i ^ r) hw hw' hzr_nn hq
  -- Simplify: (zᵢ^r)^(t/r) = zᵢ^t
  have simp_sum : ∑ i ∈ s, w i * (z i ^ r) ^ (t / r) = ∑ i ∈ s, w i * z i ^ t :=
    Finset.sum_congr rfl fun i hi => by
      congr 1
      rw [← Real.rpow_mul (le_of_lt (hz i hi))]
      congr 1
      field_simp
  rw [simp_sum] at jensen
  -- Σ wᵢ zᵢ^r ≥ 0 and Σ wᵢ zᵢ^t ≥ 0
  have hsum_r : 0 ≤ ∑ i ∈ s, w i * z i ^ r :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (le_of_lt (hz i hi)) r)
  -- Raise both sides to 1/t > 0
  have hmono : ((∑ i ∈ s, w i * z i ^ r) ^ (t / r)) ^ (1 / t) ≤
               (∑ i ∈ s, w i * z i ^ t) ^ (1 / t) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hsum_r _) jensen (by positivity)
  -- Simplify LHS: ((Σ wᵢ zᵢ^r)^(t/r))^(1/t) = (Σ wᵢ zᵢ^r)^(1/r)
  have lhs_simp : ((∑ i ∈ s, w i * z i ^ r) ^ (t / r)) ^ (1 / t) =
                  (∑ i ∈ s, w i * z i ^ r) ^ (1 / r) := by
    rw [← Real.rpow_mul hsum_r]
    congr 1
    field_simp
  rw [lhs_simp] at hmono
  exact hmono

/-- **Power Mean Monotonicity** (general statement, partially proved).

For r ≤ s with r, s ≠ 0, M_r(z, w) ≤ M_s(z, w).

**Status**:
- `power_mean_monotone_pos` proves this for 0 < r ≤ s.
- The negative r case (r < 0 or mixed signs) requires additional work.
- Mathlib4 has a TODO for this: "generalized mean inequality with any p ≤ q,
  including negative numbers" (Mathlib.Analysis.MeanInequalities). -/
axiom power_mean_monotone
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r s_exp : ℝ} (hrs : r ≤ s_exp)
    (hr : r ≠ 0) (hs : s_exp ≠ 0) :
    weightedPowerMean s w z r hr ≤ weightedPowerMean s w z s_exp hs

/-- **Harmonic Mean ≤ Geometric Mean** (proved via `harmonic_mean_le_geom_mean_direct`).

The `hHM` hypothesis documents the connection between M_{-1} and the harmonic mean
formula, but the inequality itself is proved without using the power mean axiom. -/
theorem harmonic_mean_le_geom_mean_via_power
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    (_hHM : weightedPowerMean s w z (-1) (by norm_num) = (∑ i ∈ s, w i * (z i)⁻¹)⁻¹) :
    (∑ i ∈ s, w i * (z i)⁻¹)⁻¹ ≤ weightedGeomMean s w z :=
  harmonic_mean_le_geom_mean_direct s w z hw hw' hz

/-- **Summary: The Interpolation Chain**.

The power means M_r form a continuous monotone family in r ∈ [-∞, +∞]:

    min(z) ≤ ... ≤ HM = M_{-1} ≤ GM = M_0 ≤ AM = M_1 ≤ M_2 ≤ ... ≤ max(z)

Key proved relationships:
- [✓] GM ≤ AM  (`geom_mean_le_arith_mean` — from Mathlib)
- [✓] AM ≤ M_p for p ≥ 1  (`arith_mean_le_power_mean` — from Mathlib)
- [✓] GM ≤ M_p for p ≥ 1  (`geom_mean_le_power_mean_of_one_le`)
- [✓] Jensen's inequality  (`jensen_pow_ineq` — from Mathlib)
- [✓] HM ≤ GM  (`harmonic_mean_le_geom_mean_direct` — proved here)
- [✓] M_r ≤ M_s for 0 < r ≤ s  (`power_mean_monotone_pos` — proved here)
- [axiom] General monotonicity for negative r (open in Mathlib4 as of 2026) -/
theorem power_mean_interpolation_summary : True := trivial
