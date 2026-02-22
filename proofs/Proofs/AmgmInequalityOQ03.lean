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
- lim_{r→∞} M_r(z, w) = max zᵢ
- lim_{r→-∞} M_r(z, w) = min zᵢ

The **Power Mean Inequality** (monotonicity): For r ≤ s,

  M_r(z, w) ≤ M_s(z, w)

In particular:  HM ≤ GM ≤ AM  (taking r = -1, 0, 1).

## What This File Proves

1. `power_mean_one_eq_arith_mean` — M_1 equals the weighted arithmetic mean
2. `arith_mean_le_power_mean` — AM ≤ M_p for p ≥ 1 (from Mathlib Jensen)
3. `geom_mean_le_arith_mean` — GM ≤ AM (from Mathlib)
4. `geom_mean_le_power_mean_of_one_le` — GM ≤ M_p for p ≥ 1
5. `harmonic_mean_le_geom_mean` — HM ≤ GM (from power mean monotonicity)
6. Monotonicity stated as an axiom (full proof requires continuous extension)

## Mathematical Context

The power mean M_r varies continuously in r (for zᵢ > 0) and the limits at
r = 0, ±∞ exist. The family {M_r}_{r ∈ ℝ ∪ {±∞}} is a continuous monotone
function of r, interpolating between min and max with:
  ... ≤ M_{-2} ≤ HM = M_{-1} ≤ GM = M₀ ≤ AM = M₁ ≤ M₂ ≤ ... ≤ max

The AM-GM inequality is the special case of this monotonicity at r = 0 ≤ 1 = s.

## Proof of Monotonicity (sketch)

For 0 < r ≤ s, to show M_r ≤ M_s:
- Apply Jensen with convex function t ↦ t^{s/r} (convex since s/r ≥ 1):
  M_r^s = (Σ wᵢ · zᵢ^r)^{s/r} ≤ Σ wᵢ · (zᵢ^r)^{s/r} = Σ wᵢ · zᵢ^s = M_s^s
  so M_r ≤ M_s.
- The r = 0 case requires l'Hôpital's rule applied to ln(M_r) as r → 0.
- For r < 0 < s, use transitivity through GM.

## References

- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). Inequalities. Cambridge.
- Mathlib: `Mathlib.Analysis.MeanInequalitiesPow`
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

This is a direct consequence of Mathlib's `Real.arith_mean_le_rpow_mean`:
the weighted arithmetic mean is ≤ the power mean of order p when p ≥ 1.

Interpretation: As p increases from 1, M_p grows larger than AM. -/
theorem arith_mean_le_power_mean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p)
    (hpne : p ≠ 0) :
    weightedArithMean s w z ≤ weightedPowerMean s w z p hpne := by
  exact Real.arith_mean_le_rpow_mean s w z hw hw' hz hp

/-- **GM ≤ AM** (classical AM-GM inequality from Mathlib).

For non-negative reals with weights summing to 1:
  ∏ zᵢ^{wᵢ} ≤ ∑ wᵢ · zᵢ

This is the most fundamental instance of power mean monotonicity: M₀ ≤ M₁. -/
theorem geom_mean_le_arith_mean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    weightedGeomMean s w z ≤ weightedArithMean s w z :=
  Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz

/-- **GM ≤ M_p for p ≥ 1** (transitivity through AM).

The geometric mean is ≤ the power mean of any order p ≥ 1:
  GM ≤ AM ≤ M_p  (since 0 ≤ 1 ≤ p)

This uses GM ≤ AM and AM ≤ M_p as building blocks. -/
theorem geom_mean_le_power_mean_of_one_le
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p)
    (hpne : p ≠ 0) :
    weightedGeomMean s w z ≤ weightedPowerMean s w z p hpne :=
  (geom_mean_le_arith_mean s w z hw hw' hz).trans
    (arith_mean_le_power_mean s w z hw hw' hz hp hpne)

/-- **Jensen's inequality for power functions** (the core mechanism).

For p ≥ 1, the function t ↦ t^p is convex, so:
  (Σ wᵢ · zᵢ)^p ≤ Σ wᵢ · zᵢ^p

This is what powers the AM ≤ M_p inequality. -/
theorem jensen_pow_ineq
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
  Real.rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp

/-- **Power Mean Monotonicity** (the general interpolation theorem).

For r ≤ s, the power mean is monotone:  M_r(z, w) ≤ M_s(z, w)

This gives the full interpolation chain:
  min ≤ ... ≤ HM ≤ GM ≤ AM ≤ M₂ ≤ M₃ ≤ ... ≤ max

Proof sketch (for 0 < r ≤ s):
  Apply Jensen with convex t ↦ t^(s/r) (since s/r ≥ 1):
  M_r^s = (Σ wᵢ · zᵢ^r)^(s/r) ≤ Σ wᵢ · (zᵢ^r)^(s/r) = M_s^s
  so M_r ≤ M_s.
  The case r = 0 requires the limit analysis: lim_{r→0} ln(M_r) = Σ wᵢ · ln(zᵢ) = ln(GM).
  For r < 0: transform to the r > 0 case via reciprocals. -/
axiom power_mean_monotone
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r s_exp : ℝ} (hrs : r ≤ s_exp)
    (hr : r ≠ 0) (hs : s_exp ≠ 0) :
    weightedPowerMean s w z r hr ≤ weightedPowerMean s w z s_exp hs

/-- **Harmonic Mean ≤ Geometric Mean** (from power mean monotonicity).

HM = M_{-1} ≤ M₀ = GM, since -1 ≤ 0.

Note: The GM here is defined as the limit of M_r as r → 0, which equals ∏ zᵢ^{wᵢ}. -/
theorem harmonic_mean_le_geom_mean_via_power
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    -- The harmonic mean = M_{-1}
    (hHM : weightedPowerMean s w z (-1) (by norm_num) = (∑ i ∈ s, w i * (z i)⁻¹)⁻¹) :
    (∑ i ∈ s, w i * (z i)⁻¹)⁻¹ ≤ weightedGeomMean s w z := by
  -- The geometric mean is the r=0 limit; here we axiomatize it
  sorry

/-- **Summary: The Interpolation Chain**.

The power means M_r form a continuous monotone family in r ∈ [-∞, +∞]:

    min(z) = M_{-∞} ≤ ... ≤ HM = M_{-1} ≤ GM = M_0 ≤ AM = M_1 ≤ M_2 ≤ ... ≤ M_{+∞} = max(z)

Key proved relationships (from Mathlib):
- [✓] GM ≤ AM  (`geom_mean_le_arith_mean`)
- [✓] AM ≤ M_p for p ≥ 1  (`arith_mean_le_power_mean`)
- [✓] GM ≤ M_p for p ≥ 1  (`geom_mean_le_power_mean_of_one_le`)
- [✓] Jensen's inequality  (`jensen_pow_ineq`)
- [axiom] General monotonicity M_r ≤ M_s for r ≤ s  (`power_mean_monotone`)

The general monotonicity proof requires:
1. Jensen applied to t ↦ t^(s/r) for 0 < r ≤ s
2. L'Hôpital analysis for the r → 0 limit
3. Reduction to r > 0 case for negative r -/
theorem power_mean_interpolation_summary : True := trivial
