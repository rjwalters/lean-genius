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

/-- **Algebraic identity**: For r ≠ 0 and z_i > 0,
  M_r(z, w) = M_{-r}(z⁻¹, w)⁻¹

The power mean of order r equals the reciprocal of the power mean of order -r
applied to the reciprocal values.

**Proof**:
- Sum: (zᵢ⁻¹)^{-r} = zᵢ^r (via inv_rpow + rpow_neg + inv_inv)
- Power: A^{1/r} = (A^{1/(-r)})⁻¹ (since 1/(-r) = -(1/r) and rpow_neg + inv_inv) -/
lemma power_mean_neg_inv
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hz : ∀ i ∈ s, 0 < z i)
    {r : ℝ} (hr : r ≠ 0) :
    weightedPowerMean s w z r hr =
      (weightedPowerMean s w (fun i => (z i)⁻¹) (-r) (neg_ne_zero.mpr hr))⁻¹ := by
  simp only [weightedPowerMean]
  -- Step 1: (zᵢ⁻¹)^{-r} = zᵢ^r
  have sum_eq : ∑ i ∈ s, w i * (z i)⁻¹ ^ (-r) = ∑ i ∈ s, w i * z i ^ r := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [Real.inv_rpow (le_of_lt (hz i hi)) (-r),
        Real.rpow_neg (le_of_lt (hz i hi)) r,
        inv_inv]
  -- A = ∑ wᵢ zᵢ^r ≥ 0
  have hA_nn : 0 ≤ ∑ i ∈ s, w i * z i ^ r :=
    Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (Real.rpow_nonneg (le_of_lt (hz i hi)) r)
  -- Step 2: A^{1/r} = (A^{1/(-r)})⁻¹ since 1/(-r) = -(1/r)
  rw [sum_eq, show (1 : ℝ) / (-r) = -(1 / r) from by ring,
      Real.rpow_neg hA_nn, inv_inv]

/-- Helper: ∑ wᵢ zᵢ^p > 0 when weights sum to 1 and all zᵢ > 0. -/
private lemma weighted_sum_pos
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {p : ℝ} :
    0 < ∑ i ∈ s, w i * z i ^ p := by
  -- Since ∑ wᵢ = 1 > 0 and all wᵢ ≥ 0, some wᵢ₀ > 0
  obtain ⟨i₀, hi₀, hwi₀⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra h
    push_neg at h
    have hw_zero : ∀ i ∈ s, w i = 0 := fun i hi => le_antisymm (h i hi) (hw i hi)
    linarith [Finset.sum_eq_zero hw_zero]
  -- The term for i₀ is positive; the sum is at least that term
  exact lt_of_lt_of_le
    (mul_pos hwi₀ (Real.rpow_pos_of_pos (hz i₀ hi₀) p))
    (Finset.single_le_sum
      (fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (le_of_lt (hz i hi)) p))
      hi₀)

/-- Helper: The weighted power mean is positive when weights sum to 1 and zᵢ > 0. -/
private lemma weightedPowerMean_pos
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {p : ℝ} (hp : p ≠ 0) :
    0 < weightedPowerMean s w z p hp :=
  Real.rpow_pos_of_pos (weighted_sum_pos s w z hw hw' hz) (1 / p)

/-- **Power Mean Monotonicity for r ≤ s < 0** (dual argument, fully proved).

For r ≤ s with both negative, M_r(z,w) ≤ M_s(z,w).

**Proof**: Let z' = z⁻¹. Since r ≤ s < 0, we have 0 < -s ≤ -r.
By `power_mean_monotone_pos` applied to z' with exponents -s ≤ -r:
  M_{-s}(z', w) ≤ M_{-r}(z', w)
By `power_mean_neg_inv`: M_r(z) = M_{-r}(z')⁻¹ and M_s(z) = M_{-s}(z')⁻¹.
Since 0 < M_{-s}(z') ≤ M_{-r}(z'), inverting reverses the inequality:
  M_r(z) = M_{-r}(z')⁻¹ ≤ M_{-s}(z')⁻¹ = M_s(z). -/
theorem power_mean_monotone_neg
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hrt : r ≤ t) (ht : t < 0)
    (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedPowerMean s w z t htne := by
  have hr : r < 0 := lt_of_le_of_lt hrt ht
  have hnr_pos : 0 < -r := neg_pos.mpr hr
  have hnt_pos : 0 < -t := neg_pos.mpr ht
  have hnrt : -t ≤ -r := neg_le_neg hrt
  have hzinv : ∀ i ∈ s, 0 < (fun i => (z i)⁻¹) i :=
    fun i hi => inv_pos.mpr (hz i hi)
  -- Use consistent nonzero proofs throughout
  have hrne_neg : -r ≠ 0 := neg_ne_zero.mpr hrne
  have htne_neg : -t ≠ 0 := neg_ne_zero.mpr htne
  -- M_{-t}(z⁻¹) ≤ M_{-r}(z⁻¹) by power_mean_monotone_pos
  have h_mono : weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg ≤
                weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hrne_neg :=
    power_mean_monotone_pos s w (fun i => (z i)⁻¹) hw hw' hzinv hnt_pos hnrt
      htne_neg hrne_neg
  -- Both power means are positive
  have h_neg_t_pos : 0 < weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg :=
    weightedPowerMean_pos s w (fun i => (z i)⁻¹) hw hw' hzinv htne_neg
  have h_neg_r_pos : 0 < weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hrne_neg :=
    weightedPowerMean_pos s w (fun i => (z i)⁻¹) hw hw' hzinv hrne_neg
  -- Convert M_r(z) and M_t(z) using the dual identity
  rw [power_mean_neg_inv s w z hw hz hrne, power_mean_neg_inv s w z hw hz htne]
  -- Goal: M_{-r}(z⁻¹)⁻¹ ≤ M_{-t}(z⁻¹)⁻¹
  -- i.e., B⁻¹ ≤ A⁻¹ where A = M_{-t}(z⁻¹) ≤ B = M_{-r}(z⁻¹), 0 < A
  -- Step: prove 1 ≤ A⁻¹ * B, then multiply both sides by B⁻¹
  have h_t_ne : weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg ≠ 0 :=
    ne_of_gt h_neg_t_pos
  have h_r_ne : weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hrne_neg ≠ 0 :=
    ne_of_gt h_neg_r_pos
  have key : 1 ≤
      (weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg)⁻¹ *
      (weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hrne_neg) :=
    calc (1 : ℝ)
        = (weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg) *
          (weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg)⁻¹ :=
            (mul_inv_cancel₀ h_t_ne).symm
      _ ≤ (weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hrne_neg) *
          (weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg)⁻¹ :=
            mul_le_mul_of_nonneg_right h_mono
              (inv_nonneg.mpr (le_of_lt h_neg_t_pos))
      _ = (weightedPowerMean s w (fun i => (z i)⁻¹) (-t) htne_neg)⁻¹ *
          (weightedPowerMean s w (fun i => (z i)⁻¹) (-r) hrne_neg) :=
            mul_comm _ _
  have step := mul_le_mul_of_nonneg_right key
    (inv_nonneg.mpr (le_of_lt h_neg_r_pos))
  rw [one_mul] at step
  rwa [mul_assoc, mul_inv_cancel₀ h_r_ne, mul_one] at step

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

/-
Summary: The Interpolation Chain.

The power means M_r form a continuous monotone family in r ∈ [-∞, +∞]:

    min(z) ≤ ... ≤ HM = M_{-1} ≤ GM = M_0 ≤ AM = M_1 ≤ M_2 ≤ ... ≤ max(z)

Key proved relationships:
- GM ≤ AM  (geom_mean_le_arith_mean — from Mathlib)
- AM ≤ M_p for p ≥ 1  (arith_mean_le_power_mean — from Mathlib)
- GM ≤ M_p for p ≥ 1  (geom_mean_le_power_mean_of_one_le)
- Jensen's inequality  (jensen_pow_ineq — from Mathlib)
- HM ≤ GM  (harmonic_mean_le_geom_mean_direct — proved here)
- M_r ≤ M_s for 0 < r ≤ s  (power_mean_monotone_pos — proved here)
- M_r ≤ M_s for r ≤ s < 0  (power_mean_monotone_neg — proved here via dual argument)
- Mixed-sign case (r < 0 < s, crossing the geometric mean limit) is an axiom.
-/
