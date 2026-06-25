/-
# Power Mean Monotonicity: The Mixed-Sign Case M_r ≤ M_s for r < 0 < s

## Open Question: amgm-inequality-oq-03-oq-01-oq-01

The parent file `AmgmInequalityOQ03.lean` proves power-mean monotonicity in two
regimes that do *not* cross zero:

  * `power_mean_monotone_pos` — M_r ≤ M_s for 0 < r ≤ s, and
  * `power_mean_monotone_neg` — M_r ≤ M_s for r ≤ s < 0.

It explicitly leaves open the **mixed-sign case** r < 0 < s, where the comparison
must cross the geometric-mean limit at the exponent 0. This file closes that gap.

## Result

For positive reals z₁,…,zₙ with nonnegative weights w₁,…,wₙ summing to 1, and any
exponents r < 0 < s,

  M_r(z, w) ≤ M_s(z, w),

where M_p(z, w) = (∑ᵢ wᵢ zᵢ^p)^{1/p} is the weighted power mean of order p.

## Proof Strategy

We route the comparison through the **weighted geometric mean** GM = ∏ zᵢ^{wᵢ},
which is precisely lim_{p→0} M_p. The single Mathlib analytic input is the weighted
arithmetic–geometric mean inequality `Real.geom_mean_le_arith_mean_weighted`:

  ∏ yᵢ^{wᵢ} ≤ ∑ wᵢ yᵢ.

Applied to yᵢ = zᵢ^p, together with the identity ∏ (zᵢ^p)^{wᵢ} = GM^p, this yields
the single *core estimate*

  GM^p ≤ ∑ wᵢ zᵢ^p   for every exponent p.            (★)

Now the sign of p controls the direction of the comparison after taking 1/p-th powers:

  * For **s > 0** the map t ↦ t^{1/s} is increasing, so (★) gives GM ≤ M_s.
  * For **r < 0** the map t ↦ t^{1/r} is decreasing, so (★) *reverses* to M_r ≤ GM.

Chaining,  M_r ≤ GM ≤ M_s.

The crossing of zero is exactly the sign flip of 1/p — which is why the two
same-sign theorems of the parent file cannot be combined directly: there is no
common exponent between a negative r and a positive s to transit through, except
the degenerate order 0 represented by the geometric mean itself.

## What This File Proves

1. `geomMean_rpow_le_weighted_sum` — the core estimate (★): GM^p ≤ ∑ wᵢ zᵢ^p.
2. `geomMean_le_powerMean_pos` — GM ≤ M_s for s > 0.
3. `powerMean_le_geomMean_neg` — M_r ≤ GM for r < 0.
4. `power_mean_monotone_mixed` — M_r ≤ M_s for r < 0 < s (the open question).

## References

- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). *Inequalities*. Cambridge.
- Mathlib: `Real.geom_mean_le_arith_mean_weighted` (Mathlib.Analysis.MeanInequalities).
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Proofs.AmgmInequalityOQ03

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-- **Core estimate (★)**: for *every* exponent `p`, the `p`-th power of the weighted
geometric mean `GM = ∏ zᵢ^{wᵢ}` is bounded by the weighted arithmetic mean of the
`p`-th powers:

  `GM ^ p ≤ ∑ᵢ wᵢ · zᵢ ^ p`.

This is the sole use of Mathlib's weighted AM-GM inequality
`Real.geom_mean_le_arith_mean_weighted`, applied to the values `yᵢ = zᵢ ^ p`,
combined with the identity `∏ (zᵢ ^ p) ^ wᵢ = (∏ zᵢ ^ wᵢ) ^ p`. Note the
inequality holds for *all* real `p`, including negative ones; the direction of
the resulting mean comparison only emerges after raising to the power `1/p`. -/
theorem geomMean_rpow_le_weighted_sum
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    (p : ℝ) :
    (weightedGeomMean s w z) ^ p ≤ ∑ i ∈ s, w i * z i ^ p := by
  have hz_nn : ∀ i ∈ s, 0 ≤ z i := fun i hi => (hz i hi).le
  -- Weighted AM-GM applied to the values yᵢ = zᵢ^p.
  have key := Real.geom_mean_le_arith_mean_weighted s w (fun i => z i ^ p) hw hw'
    (fun i hi => Real.rpow_nonneg (hz_nn i hi) p)
  -- key : ∏ (zᵢ^p)^wᵢ ≤ ∑ wᵢ * zᵢ^p.
  -- Rewrite the left-hand product into GM^p.
  have lhs_eq : ∏ i ∈ s, (z i ^ p) ^ w i = (weightedGeomMean s w z) ^ p := by
    have hterm : ∀ i ∈ s, (z i ^ p) ^ w i = (z i ^ w i) ^ p := by
      intro i hi
      rw [← Real.rpow_mul (hz_nn i hi), ← Real.rpow_mul (hz_nn i hi), mul_comm p (w i)]
    rw [Finset.prod_congr rfl hterm,
        Real.finset_prod_rpow s (fun i => z i ^ w i)
          (fun i hi => Real.rpow_nonneg (hz_nn i hi) _) p,
        weightedGeomMean]
  rwa [lhs_eq] at key

/-- **GM ≤ M_s for positive order** `s > 0`. Raising the core estimate (★)
`GM^s ≤ ∑ wᵢ zᵢ^s` to the positive power `1/s` (which preserves the inequality)
gives `GM ≤ (∑ wᵢ zᵢ^s)^{1/s} = M_s`. -/
theorem geomMean_le_powerMean_pos
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {p : ℝ} (hp : 0 < p) (hpne : p ≠ 0) :
    weightedGeomMean s w z ≤ weightedPowerMean s w z p hpne := by
  have hGM_pos : 0 < weightedGeomMean s w z := by
    rw [weightedGeomMean]
    exact Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (hz i hi) _)
  have core := geomMean_rpow_le_weighted_sum s w z hw hw' hz p
  have h1p : (0 : ℝ) ≤ 1 / p := by positivity
  -- Raise both sides of (★) to the nonnegative power 1/p (monotone).
  have step := Real.rpow_le_rpow (Real.rpow_nonneg hGM_pos.le p) core h1p
  rw [weightedPowerMean]
  -- (GM^p)^(1/p) = GM since p ≠ 0.
  rwa [← Real.rpow_mul hGM_pos.le, mul_one_div_cancel hpne, Real.rpow_one] at step

/-- **M_r ≤ GM for negative order** `r < 0`. Raising the core estimate (★)
`GM^r ≤ ∑ wᵢ zᵢ^r` to the *negative* power `1/r` *reverses* the inequality, giving
`M_r = (∑ wᵢ zᵢ^r)^{1/r} ≤ GM`. The sign flip of `1/r` is the heart of the
mixed-sign case. -/
theorem powerMean_le_geomMean_neg
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {p : ℝ} (hp : p < 0) (hpne : p ≠ 0) :
    weightedPowerMean s w z p hpne ≤ weightedGeomMean s w z := by
  have hGM_pos : 0 < weightedGeomMean s w z := by
    rw [weightedGeomMean]
    exact Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (hz i hi) _)
  have core := geomMean_rpow_le_weighted_sum s w z hw hw' hz p
  have h1p : 1 / p ≤ 0 := (div_neg_of_pos_of_neg one_pos hp).le
  -- Raise both sides of (★) to the nonpositive power 1/p (antitone): direction reverses.
  have step := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hGM_pos p) core h1p
  rw [weightedPowerMean]
  -- (GM^p)^(1/p) = GM since p ≠ 0; the base GM fixes the rewrite to the RHS only.
  rwa [← Real.rpow_mul hGM_pos.le, mul_one_div_cancel hpne, Real.rpow_one] at step

/-- **Power-Mean Monotonicity, mixed-sign case** — closes
`amgm-inequality-oq-03-oq-01-oq-01`.

For positive reals with weights summing to 1, and exponents `r < 0 < t`,

  M_r(z, w) ≤ M_t(z, w).

The comparison crosses the geometric-mean limit at order 0: `M_r ≤ GM ≤ M_t`. -/
theorem power_mean_monotone_mixed
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : r < 0) (ht : 0 < t)
    (hrne : r ≠ 0) (htne : t ≠ 0) :
    weightedPowerMean s w z r hrne ≤ weightedPowerMean s w z t htne :=
  le_trans
    (powerMean_le_geomMean_neg s w z hw hw' hz hr hrne)
    (geomMean_le_powerMean_pos s w z hw hw' hz ht htne)
