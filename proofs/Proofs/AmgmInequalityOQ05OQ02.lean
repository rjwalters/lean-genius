/-
  The weighted AM-GM inequality: its equality case for `n` terms.

  For strictly positive weights `w : ι → ℝ` summing to `1` over a finite index
  set `t` and strictly positive reals `x : ι → ℝ`, the weighted arithmetic mean
  dominates the weighted geometric mean,

      ∏ i ∈ t, (x i) ^ (w i)  ≤  ∑ i ∈ t, w i * x i.

  This file pins down the **equality case**: equality holds **iff every `xⱼ`
  equals the weighted mean**, equivalently iff all the `xⱼ` are equal.

  The parent entry proved the two-variable pointwise Young equality case from the
  strict convexity of `exp`; one of its stated open questions was to upgrade this
  to the `n`-term weighted AM-GM equality case "again via strict convexity of
  `exp`".  That is exactly what we do here, in the dual (and equivalent) form:
  the logarithm is *strictly concave* on `(0, ∞)`, so Jensen's inequality for
  `Real.log` is strict unless all evaluation points coincide.  Concretely we
  take logs to turn the multiplicative AM-GM equality into the additive Jensen
  equality

      Real.log (∑ wᵢ xᵢ)  =  ∑ wᵢ · Real.log (xᵢ),

  and feed it to Mathlib's canonical equality-case lemma
  `StrictConcaveOn.map_sum_eq_iff` for the strictly concave `Real.log`
  (`strictConcaveOn_log_Ioi`).  Mathlib has the weighted AM-GM inequality and the
  strict Jensen machinery, but does not package this particular equality
  characterisation of the geometric/arithmetic mean.

  All exponents are real, so `^` denotes `Real.rpow` throughout.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib

open Real Finset

namespace AmgmInequalityOQ05OQ02

variable {ι : Type*}

/-- Taking logs turns the weighted geometric mean into the weighted sum of
logarithms: `log (∏ xᵢ ^ wᵢ) = ∑ wᵢ · log xᵢ`. -/
theorem log_prod_rpow {t : Finset ι} {w x : ι → ℝ} (hx : ∀ i ∈ t, 0 < x i) :
    Real.log (∏ i ∈ t, x i ^ w i) = ∑ i ∈ t, w i * Real.log (x i) := by
  rw [Real.log_prod (fun i hi => (Real.rpow_pos_of_pos (hx i hi) (w i)).ne')]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Real.log_rpow (hx i hi)]

/-- The weighted geometric mean of positive reals is positive. -/
theorem prod_rpow_pos {t : Finset ι} {w x : ι → ℝ} (hx : ∀ i ∈ t, 0 < x i) :
    0 < ∏ i ∈ t, x i ^ w i :=
  Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (hx i hi) (w i))

/-- The weighted arithmetic mean of positive reals with positive weights, over a
nonempty index set, is positive. -/
theorem mean_pos {t : Finset ι} {w x : ι → ℝ} (hw : ∀ i ∈ t, 0 < w i)
    (hx : ∀ i ∈ t, 0 < x i) (hne : t.Nonempty) :
    0 < ∑ i ∈ t, w i * x i :=
  Finset.sum_pos (fun i hi => mul_pos (hw i hi) (hx i hi)) hne

/-- **Equality case of the weighted AM-GM inequality (canonical form).**

For strictly positive weights summing to `1` and strictly positive `x`, the
weighted geometric mean equals the weighted arithmetic mean **iff every `xⱼ`
equals that common mean**. -/
theorem weighted_amgm_eq_iff {t : Finset ι} {w x : ι → ℝ} (hw : ∀ i ∈ t, 0 < w i)
    (hsum : ∑ i ∈ t, w i = 1) (hx : ∀ i ∈ t, 0 < x i) :
    (∏ i ∈ t, x i ^ w i = ∑ i ∈ t, w i * x i) ↔
      (∀ j ∈ t, x j = ∑ i ∈ t, w i * x i) := by
  -- A sum of weights equal to `1` forces the index set to be nonempty.
  have hne : t.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hsum
  have hA : 0 < ∑ i ∈ t, w i * x i := mean_pos hw hx hne
  have hP : 0 < ∏ i ∈ t, x i ^ w i := prod_rpow_pos hx
  -- Both means are positive, so the equality is equivalent to its image under `log`.
  rw [← Real.log_injOn_pos.eq_iff (Set.mem_Ioi.mpr hP) (Set.mem_Ioi.mpr hA),
      log_prod_rpow hx, eq_comm]
  -- The strict concavity of `log` supplies the equality case of Jensen.
  have key := strictConcaveOn_log_Ioi.map_sum_eq_iff (t := t) (w := w) (p := x)
      hw hsum (fun i hi => Set.mem_Ioi.mpr (hx i hi))
  simpa only [smul_eq_mul] using key

/-- **Equality case of the weighted AM-GM inequality (pairwise form).**

Equality holds iff all the `xⱼ` (over the support of the weights) are equal. -/
theorem weighted_amgm_eq_iff_pairwise {t : Finset ι} {w x : ι → ℝ}
    (hw : ∀ i ∈ t, 0 < w i) (hsum : ∑ i ∈ t, w i = 1) (hx : ∀ i ∈ t, 0 < x i) :
    (∏ i ∈ t, x i ^ w i = ∑ i ∈ t, w i * x i) ↔
      (∀ i ∈ t, ∀ j ∈ t, x i = x j) := by
  rw [weighted_amgm_eq_iff hw hsum hx]
  constructor
  · intro h i hi j hj
    rw [h i hi, h j hj]
  · intro h j hj
    have hconst : ∑ i ∈ t, w i * x i = ∑ i ∈ t, w i * x j := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [h i hi j hj]
    rw [hconst, ← Finset.sum_mul, hsum, one_mul]

/-- The trivial direction, recorded explicitly: if all `xⱼ` are equal then the
weighted geometric and arithmetic means coincide. -/
theorem weighted_amgm_eq_of_const {t : Finset ι} {w x : ι → ℝ} {c : ℝ}
    (hw : ∀ i ∈ t, 0 < w i) (hsum : ∑ i ∈ t, w i = 1) (hx : ∀ i ∈ t, 0 < x i)
    (hc : ∀ i ∈ t, x i = c) :
    ∏ i ∈ t, x i ^ w i = ∑ i ∈ t, w i * x i :=
  (weighted_amgm_eq_iff_pairwise hw hsum hx).mpr
    (fun i hi j hj => (hc i hi).trans (hc j hj).symm)

end AmgmInequalityOQ05OQ02
