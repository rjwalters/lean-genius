import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRight
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
# Joint Continuity of `curvatureSin K t` in Both Curvature `K` and Parameter `t` (OQ-03)

## What This Proves

The parent entry (`SynthesisCurvaturePtolemy.lean`) defines the curvature-parametrized
sine function

  `curvatureSin K t =`
    `t`                         if `K = 0`   (Euclidean),
    `sin(√K · t) / √K`          if `K > 0`   (spherical),
    `sinh(√(−K) · t) / √(−K)`   if `K < 0`   (hyperbolic),

which unifies the three constant-curvature geometries.  The parent proves
properties for *fixed* `K` (the ODE, the derivative at `0`, special values).  This
entry proves the **joint continuity** of the map

  `(K, t) ↦ curvatureSin K t`

as a function `ℝ × ℝ → ℝ`.  This is the precise sense in which "the three geometries
vary continuously with the curvature": there is no discontinuity at the Euclidean
seam `K = 0`, even though the defining *formula* switches there between `sin` and
`sinh`.

## The argument

The piecewise definition makes a direct two-variable seam analysis awkward, so we
factor the seam into a single real variable.  Define the **curvature sinc**

  `curvatureSinc x =`
    `1`                         if `x = 0`,
    `sin(√x) / √x`              if `x > 0`,
    `sinh(√(−x)) / √(−x)`       if `x < 0`,

and prove the algebraic identity

  `curvatureSin K t = t · curvatureSinc (K · t²)`   (`curvatureSin_eq`).

The identity collapses the three branches of `curvatureSin` (with their `±` sign
bookkeeping from the oddness of `sin`/`sinh`) onto the three branches of the *even*
function `curvatureSinc`, using `√(K t²) = √K · |t|`.

Continuity then reduces to two facts:

* `curvatureSinc` is continuous at every `x ≠ 0` (a quotient of continuous functions,
  the denominator being nonzero there); and
* `curvatureSinc` is continuous at the seam `x = 0`.  Here the two one-sided limits
  are both `1`: from the right `sin(√x)/√x → 1` and from the left `sinh(√(−x))/√(−x)
  → 1`, each obtained from the *slope-to-derivative* characterisation
  (`HasDerivAt.tendsto_slope`) applied to `sin` and `sinh` at `0` — i.e. `sin' 0 =
  cos 0 = 1` and `sinh' 0 = cosh 0 = 1`.  The two punctured-neighbourhood limits are
  glued via `𝓝[<] 0 ⊔ 𝓝[>] 0 = 𝓝[≠] 0` and lifted to `ContinuousAt` through
  `continuousAt_iff_punctured_nhds`.

Joint continuity of `(K, t) ↦ t · curvatureSinc (K t²)` is then immediate from
continuity of `curvatureSinc` and the ring operations.

## What Mathlib has — and what this adds

Mathlib has `continuous_sin`, `continuous_sinh`, `Real.continuous_sqrt`, the slope
characterisation of the derivative, and the order/topology gluing lemmas, but it has
no `curvatureSin`/`curvatureSinc` and hence nothing about the continuity of the
constant-curvature `sn_K` family across the curvature seam.  The new content is the
single-variable factorisation `curvatureSin_eq`, the continuity of `curvatureSinc`
(seam included), and the joint continuity `continuous_curvatureSin`.

**Sorry count**: 0.  **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

open Filter Topology

namespace SynthesisCurvaturePtolemyOQ03

/-- The **curvatureSin K** function, reproduced verbatim from the parent entry
`SynthesisCurvaturePtolemy.lean` so that this continuity development is
self-contained (it depends only on Mathlib):

- `K > 0` (spherical): `curvatureSin K t = sin(√K · t) / √K`
- `K = 0` (Euclidean): `curvatureSin 0 t = t`
- `K < 0` (hyperbolic): `curvatureSin K t = sinh(√(−K) · t) / √(−K)` -/
noncomputable def curvatureSin (K t : ℝ) : ℝ :=
  if K = 0 then t
  else if 0 < K then Real.sin (Real.sqrt K * t) / Real.sqrt K
  else Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)

/-- For `K > 0`, `curvatureSin K t = sin(√K · t) / √K`. -/
lemma curvatureSin_pos {K : ℝ} (hK : 0 < K) (t : ℝ) :
    curvatureSin K t = Real.sin (Real.sqrt K * t) / Real.sqrt K := by
  simp only [curvatureSin, if_neg (ne_of_gt hK), if_pos hK]

/-- For `K < 0`, `curvatureSin K t = sinh(√(−K) · t) / √(−K)`. -/
lemma curvatureSin_neg {K : ℝ} (hK : K < 0) (t : ℝ) :
    curvatureSin K t = Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K) := by
  simp only [curvatureSin, if_neg (ne_of_lt hK), if_neg (not_lt.mpr (le_of_lt hK))]

/-- The **curvature sinc** function: the even, entire "cardinal sine" underlying
`curvatureSin`.  It equals `sin(√x)/√x` for `x > 0`, `sinh(√(−x))/√(−x)` for `x < 0`,
and is normalised to `1` at the seam `x = 0` (the common value of both one-sided
limits).  The key identity `curvatureSin K t = t · curvatureSinc (K · t²)` reduces the
two-variable continuity problem to the single seam of `curvatureSinc` at `0`. -/
noncomputable def curvatureSinc (x : ℝ) : ℝ :=
  if x = 0 then 1
  else if 0 < x then Real.sin (Real.sqrt x) / Real.sqrt x
  else Real.sinh (Real.sqrt (-x)) / Real.sqrt (-x)

@[simp] lemma curvatureSinc_zero : curvatureSinc 0 = 1 := by simp [curvatureSinc]

/-- The one-variable factorisation: `curvatureSin K t = t · curvatureSinc (K · t²)`.
This is the heart of the reduction — it folds the three sign-laden branches of
`curvatureSin` onto the three branches of the even `curvatureSinc`. -/
theorem curvatureSin_eq (K t : ℝ) :
    curvatureSin K t = t * curvatureSinc (K * t ^ 2) := by
  by_cases hK : K = 0
  · subst hK; simp [curvatureSin, curvatureSinc]
  · by_cases ht : t = 0
    · subst ht; simp [curvatureSin]
    · have ht2 : (0 : ℝ) < t ^ 2 := by positivity
      rcases lt_or_gt_of_ne hK with hKneg | hKpos
      · -- K < 0 (hyperbolic branch)
        have hKt2 : K * t ^ 2 < 0 := mul_neg_of_neg_of_pos hKneg ht2
        have hsK : Real.sqrt (-K) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hKneg)
        rw [curvatureSin_neg hKneg, curvatureSinc, if_neg (ne_of_lt hKt2),
          if_neg (not_lt.mpr hKt2.le), show -(K * t ^ 2) = (-K) * t ^ 2 by ring,
          Real.sqrt_mul (neg_nonneg.mpr hKneg.le), Real.sqrt_sq_eq_abs]
        rcases lt_or_gt_of_ne ht with htneg | htpos
        · rw [abs_of_neg htneg, mul_neg, Real.sinh_neg]; field_simp
        · rw [abs_of_pos htpos]; field_simp
      · -- K > 0 (spherical branch)
        have hKt2 : (0 : ℝ) < K * t ^ 2 := mul_pos hKpos ht2
        have hsK : Real.sqrt K ≠ 0 := Real.sqrt_ne_zero'.mpr hKpos
        rw [curvatureSin_pos hKpos, curvatureSinc, if_neg (ne_of_gt hKt2),
          if_pos hKt2, Real.sqrt_mul hKpos.le, Real.sqrt_sq_eq_abs]
        rcases lt_or_gt_of_ne ht with htneg | htpos
        · rw [abs_of_neg htneg, mul_neg, Real.sin_neg]; field_simp
        · rw [abs_of_pos htpos]; field_simp

/-- `sin u / u → 1` as `u → 0` (punctured), i.e. the cardinal-sine limit, obtained
from `sin' 0 = cos 0 = 1` via the slope characterisation of the derivative. -/
private lemma tendsto_sin_div : Tendsto (fun u => Real.sin u / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope
  rw [Real.cos_zero] at h
  have heq : slope Real.sin 0 = fun u => Real.sin u / u := by
    funext u; simp [slope_def_field, Real.sin_zero]
  rwa [heq] at h

/-- `sinh u / u → 1` as `u → 0` (punctured), from `sinh' 0 = cosh 0 = 1`. -/
private lemma tendsto_sinh_div : Tendsto (fun u => Real.sinh u / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h := (Real.hasDerivAt_sinh 0).tendsto_slope
  rw [Real.cosh_zero] at h
  have heq : slope Real.sinh 0 = fun u => Real.sinh u / u := by
    funext u; simp [slope_def_field, Real.sinh_zero]
  rwa [heq] at h

/-- `√` maps the right-punctured neighbourhood of `0` into the punctured
neighbourhood of `0`. -/
private lemma tendsto_sqrt_right :
    Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Set.mem_Ioi] at hx
    exact Real.sqrt_ne_zero'.mpr hx

/-- `x ↦ √(−x)` maps the left-punctured neighbourhood of `0` into the punctured
neighbourhood of `0`. -/
private lemma tendsto_sqrt_neg_left :
    Tendsto (fun x => Real.sqrt (-x)) (𝓝[<] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun x => Real.sqrt (-x)) (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt (-0))) :=
      (Real.continuous_sqrt.comp continuous_neg).tendsto 0
    simp only [neg_zero, Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Set.mem_Iio] at hx
    exact Real.sqrt_ne_zero'.mpr (neg_pos.mpr hx)

/-- `curvatureSinc` is continuous everywhere — including across the Euclidean seam
`x = 0`, where both one-sided limits equal the value `1`. -/
theorem continuous_curvatureSinc : Continuous curvatureSinc := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- x < 0 : agrees with the (continuous) hyperbolic formula near x
    have hden : Real.sqrt (-x) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hx)
    have hcont : ContinuousAt (fun y => Real.sinh (Real.sqrt (-y)) / Real.sqrt (-y)) x :=
      ((Real.continuous_sinh.comp (Real.continuous_sqrt.comp continuous_neg)).continuousAt).div
        ((Real.continuous_sqrt.comp continuous_neg).continuousAt) hden
    refine hcont.congr ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [Set.mem_Iio] at hy
    simp only [curvatureSinc, if_neg hy.ne, if_neg (not_lt.mpr hy.le)]
  · -- x = 0 : the seam
    subst hx
    rw [continuousAt_iff_punctured_nhds, curvatureSinc_zero, ← nhdsLT_sup_nhdsGT (0 : ℝ)]
    refine tendsto_sup.mpr ⟨?_, ?_⟩
    · -- left limit via sinh
      have hcomp := tendsto_sinh_div.comp tendsto_sqrt_neg_left
      refine hcomp.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Set.mem_Iio] at hx
      simp only [Function.comp_apply, curvatureSinc, if_neg hx.ne, if_neg (not_lt.mpr hx.le)]
    · -- right limit via sin
      have hcomp := tendsto_sin_div.comp tendsto_sqrt_right
      refine hcomp.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Set.mem_Ioi] at hx
      simp only [Function.comp_apply, curvatureSinc, if_neg hx.ne', if_pos hx]
  · -- x > 0 : agrees with the (continuous) spherical formula near x
    have hden : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx
    have hcont : ContinuousAt (fun y => Real.sin (Real.sqrt y) / Real.sqrt y) x :=
      ((Real.continuous_sin.comp Real.continuous_sqrt).continuousAt).div
        (Real.continuous_sqrt.continuousAt) hden
    refine hcont.congr ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Set.mem_Ioi] at hy
    simp only [curvatureSinc, if_neg hy.ne', if_pos hy]

/-- **Joint continuity of `curvatureSin`.**  The map `(K, t) ↦ curvatureSin K t` is
continuous on all of `ℝ × ℝ`; in particular the three constant-curvature geometries
glue together continuously across the Euclidean seam `K = 0`. -/
theorem continuous_curvatureSin :
    Continuous (fun p : ℝ × ℝ => curvatureSin p.1 p.2) := by
  have hrw : (fun p : ℝ × ℝ => curvatureSin p.1 p.2)
      = fun p : ℝ × ℝ => p.2 * curvatureSinc (p.1 * p.2 ^ 2) := by
    funext p; exact curvatureSin_eq p.1 p.2
  rw [hrw]
  exact continuous_snd.mul
    (continuous_curvatureSinc.comp (continuous_fst.mul (continuous_snd.pow 2)))

/-- Restatement via `Function.uncurry`, the standard packaging of "jointly
continuous in both arguments". -/
theorem continuous_uncurry_curvatureSin :
    Continuous (Function.uncurry curvatureSin) :=
  continuous_curvatureSin

end SynthesisCurvaturePtolemyOQ03
