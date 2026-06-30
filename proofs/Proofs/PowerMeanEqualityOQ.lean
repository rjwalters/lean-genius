import Mathlib
import Proofs.AmgmInequalityOQ03
import Proofs.JensenInequalityOQ01

/-
# The Equality Case of the Power Mean Inequality

## Open Question (jensen-inequality-oq-01-oq-01-oq-01-oq-04-oq-01)

The power mean monotonicity theorem (`power_mean_monotone`, the parent result) shows that the
weighted power mean `M_p = (∑ wᵢ zᵢ^p)^{1/p}` is a *non-decreasing* function of the exponent `p`.
This file answers the sharpness question it leaves open: **when is the inequality strict?**

The answer is the classical one. For `0 < r < t`, with strictly positive weights summing to `1`
and strictly positive data,

    M_r = M_t   ↔   all the data `zᵢ` are equal.

Equivalently, `M_r < M_t` unless the data is constant. This is the exact converse companion to the
monotonicity inequality: monotonicity says `M_r ≤ M_t`, and this file pins down the equality locus.

## Proof Strategy

The engine is a single application of **strict** Jensen to the strictly convex function
`x ↦ x^{t/r}` (strictly convex on `[0,∞)` since `t/r > 1`), applied to the powered data
`uᵢ = zᵢ^r`:

    (∑ wᵢ uᵢ)^{t/r} = ∑ wᵢ uᵢ^{t/r}   ↔   every `uᵢ` equals the mean,

which is exactly `jensen_eq_iff` (the equality case of strict Jensen, from `JensenInequalityOQ01`).
The left-hand equality rewrites, via `(zᵢ^r)^{t/r} = zᵢ^t` and a monotone change of `rpow`
exponent, to `M_r = M_t`; the right-hand condition rewrites, via injectivity of `x ↦ x^r` on the
nonnegative reals, to "all `zᵢ` equal".

## Main results

* `power_mean_eq_iff_pos` — the equality case: `M_r = M_t ↔ ∀ j k, zⱼ = zₖ` (`0 < r < t`).
* `power_mean_lt_of_ne` — strict monotonicity off the diagonal: non-constant data ⇒ `M_r < M_t`.
* `am_eq_qm_iff` — `AM = QM ↔` all data equal (the `r = 1, t = 2` instance).
* `am_lt_qm_of_ne` — non-constant data ⇒ `AM < QM` strictly.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.

## Prerequisites

- `AmgmInequalityOQ03.lean`: `weightedPowerMean`, `power_mean_monotone_pos`.
- `JensenInequalityOQ01.lean`: `jensen_eq_iff` (equality case of strict Jensen).
- Mathlib: `strictConvexOn_rpow`, `Real.rpow_left_inj`, `Real.rpow_mul`.
-/

open Finset Real

namespace PowerMeanEquality

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-- The weighted power-sum `∑ wᵢ zᵢ^p` is strictly positive when the weights are nonnegative and
sum to `1` and the data is strictly positive. (Re-derived here; the analogous helper in
`AmgmInequalityOQ03` is private.) -/
private lemma wsum_pos (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) {p : ℝ} : 0 < ∑ i ∈ s, w i * z i ^ p := by
  obtain ⟨i₀, hi₀, hwi₀⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra h
    push_neg at h
    have hzero : ∀ i ∈ s, w i = 0 := fun i hi => le_antisymm (h i hi) (hw i hi)
    rw [Finset.sum_eq_zero hzero] at hw'
    norm_num at hw'
  exact lt_of_lt_of_le
    (mul_pos hwi₀ (Real.rpow_pos_of_pos (hz i₀ hi₀) p))
    (Finset.single_le_sum
      (fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hz i hi).le p)) hi₀)

/-- **Equality case of the power mean inequality.**

For `0 < r < t`, strictly positive weights summing to `1`, and strictly positive data, the two
power means coincide exactly when the data is constant:

    M_r(z, w) = M_t(z, w)   ↔   ∀ j k, zⱼ = zₖ.

This is the sharp converse to power mean monotonicity (`power_mean_monotone`). -/
theorem power_mean_eq_iff_pos
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) :
    weightedPowerMean s w z r (ne_of_gt hr)
        = weightedPowerMean s w z t (ne_of_gt (hr.trans hrt))
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have ht : 0 < t := hr.trans hrt
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hwnn : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  have hA : 0 < ∑ i ∈ s, w i * z i ^ r := wsum_pos s w z hwnn hw' hz
  have hB : 0 < ∑ i ∈ s, w i * z i ^ t := wsum_pos s w z hwnn hw' hz
  -- exponent identity used to fold `(zᵢ^r)^(t/r)` back to `zᵢ^t`
  have hrt_eq : r * (t / r) = t := by field_simp
  -- 1 < t / r ⇒ `x ↦ x^(t/r)` is strictly convex on [0,∞)
  have hgt1 : 1 < t / r := (one_lt_div hr).mpr hrt
  have hconv : StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (t / r)) :=
    strictConvexOn_rpow hgt1
  have hmem : ∀ i ∈ s, z i ^ r ∈ Set.Ici (0 : ℝ) :=
    fun i hi => Set.mem_Ici.mpr (Real.rpow_nonneg (hz i hi).le r)
  -- equality case of strict Jensen for the powered data uᵢ = zᵢ^r
  have hJ := jensen_eq_iff hconv hw hw' hmem
  simp only [smul_eq_mul] at hJ
  -- fold the right summand: ∑ wᵢ (zᵢ^r)^(t/r) = ∑ wᵢ zᵢ^t
  have hpow : ∑ i ∈ s, w i * (z i ^ r) ^ (t / r) = ∑ i ∈ s, w i * z i ^ t :=
    Finset.sum_congr rfl fun i hi => by rw [← Real.rpow_mul (hz i hi).le, hrt_eq]
  rw [hpow] at hJ
  -- bridge 1: M_r = M_t ↔ (∑ wᵢ zᵢ^r)^(t/r) = ∑ wᵢ zᵢ^t
  have eqI : weightedPowerMean s w z r hr_ne = weightedPowerMean s w z t ht_ne
      ↔ (∑ i ∈ s, w i * z i ^ r) ^ (t / r) = ∑ i ∈ s, w i * z i ^ t := by
    simp only [weightedPowerMean]
    constructor
    · intro h
      have h2 : ((∑ i ∈ s, w i * z i ^ r) ^ (1 / r)) ^ t
              = ((∑ i ∈ s, w i * z i ^ t) ^ (1 / t)) ^ t := by rw [h]
      rwa [← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le,
           show (1 / r) * t = t / r from by ring,
           show (1 / t) * t = 1 from one_div_mul_cancel ht_ne, Real.rpow_one] at h2
    · intro h
      have h2 : ((∑ i ∈ s, w i * z i ^ r) ^ (1 / r)) ^ t
              = ((∑ i ∈ s, w i * z i ^ t) ^ (1 / t)) ^ t := by
        rw [← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le,
            show (1 / r) * t = t / r from by ring,
            show (1 / t) * t = 1 from one_div_mul_cancel ht_ne, Real.rpow_one]
        exact h
      exact (Real.rpow_left_inj (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _) ht_ne).mp h2
  -- bridge 2: every zⱼ^r equals the mean ↔ all data equal
  have eqII : (∀ j ∈ s, z j ^ r = ∑ i ∈ s, w i * z i ^ r)
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k := by
    constructor
    · intro h j hj k hk
      exact (Real.rpow_left_inj (hz j hj).le (hz k hk).le hr_ne).mp
        (by rw [h j hj, h k hk])
    · intro h j hj
      calc z j ^ r
          = (∑ i ∈ s, w i) * z j ^ r := by rw [hw', one_mul]
        _ = ∑ i ∈ s, w i * z j ^ r := by rw [Finset.sum_mul]
        _ = ∑ i ∈ s, w i * z i ^ r :=
            Finset.sum_congr rfl fun i hi => by rw [h i hi j hj]
  exact eqI.trans (hJ.trans eqII)

/-- **Strict power mean inequality off the diagonal.** For `0 < r < t`, if the data is not constant
(two values differ) then the power mean inequality is strict: `M_r < M_t`. -/
theorem power_mean_lt_of_ne
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    weightedPowerMean s w z r (ne_of_gt hr)
      < weightedPowerMean s w z t (ne_of_gt (hr.trans hrt)) := by
  have hwnn : ∀ i ∈ s, 0 ≤ w i := fun i hi => (hw i hi).le
  have hle : weightedPowerMean s w z r (ne_of_gt hr)
      ≤ weightedPowerMean s w z t (ne_of_gt (hr.trans hrt)) :=
    power_mean_monotone_pos s w z hwnn hw' hz hr hrt.le (ne_of_gt hr)
      (ne_of_gt (hr.trans hrt))
  refine lt_of_le_of_ne hle ?_
  intro hEq
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  exact hjk ((power_mean_eq_iff_pos s w z hw hw' hz hr hrt).mp hEq j hj k hk)

/-- **AM = QM iff the data is constant.** Specializing the equality case to `r = 1, t = 2`: the
arithmetic mean equals the quadratic mean exactly when all the data are equal. -/
theorem am_eq_qm_iff
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) :
    weightedPowerMean s w z 1 (by norm_num) = weightedPowerMean s w z 2 (by norm_num)
      ↔ ∀ j ∈ s, ∀ k ∈ s, z j = z k :=
  power_mean_eq_iff_pos s w z hw hw' hz (by norm_num) (by norm_num)

/-- **AM < QM for non-constant data.** If two of the values differ, the arithmetic mean is strictly
below the quadratic mean. -/
theorem am_lt_qm_of_ne
    (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i)
    (hne : ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k) :
    weightedPowerMean s w z 1 (by norm_num) < weightedPowerMean s w z 2 (by norm_num) :=
  power_mean_lt_of_ne s w z hw hw' hz (by norm_num) (by norm_num) hne

end PowerMeanEquality
