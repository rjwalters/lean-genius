import Proofs.CevasTheoremNonEuclideanOQ01
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-
# Ceva non-Euclidean OQ-01-OQ-01: the flat (zero-curvature) limit of `sin_κ`

The parent entry (`cevas-theorem-non-euclidean-oq-01`) packages Ceva's theorem at an
arbitrary curvature `κ` through the **curvature sine**

`sin_κ(x) = sin(√κ·x)/√κ` (κ > 0),  `x` (κ = 0),  `sinh(√(−κ)·x)/√(−κ)` (κ < 0),

and lists as its own open question whether the curved Ceva statement degenerates
*continuously* to the Euclidean one as the curvature is sent to zero. The single missing
analytic fact is the **flat limit**

`sin_κ(x) → x   as   κ → 0`.

This file proves it, two-sidedly. The spherical branch (`κ → 0⁺`) and the hyperbolic
branch (`κ → 0⁻`) are each handled by recognising `sin(√κ·x)/√κ` and
`sinh(√(−κ)·x)/√(−κ)` as difference quotients (`slope`s at `0`) of `t ↦ sin(x·t)` and
`t ↦ sinh(x·t)`, whose derivatives at `0` are both `x` (since `cos 0 = cosh 0 = 1`). The
limit of a slope at a point is exactly the derivative, by `hasDerivAt_iff_tendsto_slope`.
A change of variables `√κ → 0⁺` (resp. `√(−κ) → 0⁺`) transports these to limits in `κ`,
and the two one-sided limits are glued — together with the exact value `sin_0(x) = x` at
`κ = 0` — into a full two-sided limit `Tendsto (sin_κ · x) (𝓝 0) (𝓝 x)`.

Consequently every curvature-`κ` Ceva ratio converges to its Euclidean counterpart as
`κ → 0`, so the curved theorem is a genuine deformation of the flat one.

## Main results

* `tendsto_sin_mul_div`   : `sin(x·t)/t → x` as `t → 0` (punctured), the spherical kernel.
* `tendsto_sinh_mul_div`  : `sinh(x·t)/t → x` as `t → 0` (punctured), the hyperbolic kernel.
* `tendsto_sinKappa_nhdsGT` : `sin_κ(x) → x` as `κ → 0⁺` (spherical flat limit).
* `tendsto_sinKappa_nhdsLT` : `sin_κ(x) → x` as `κ → 0⁻` (hyperbolic flat limit).
* `tendsto_sinKappa_punctured` : `sin_κ(x) → x` as `κ → 0`, `κ ≠ 0`.
* `tendsto_sinKappa_flat`  : `sin_κ(x) → x` as `κ → 0` (full two-sided limit).
* `sinKappa_ceva_ratio_tendsto` : a single curvature-sine ratio tends to the Euclidean one.
-/

namespace CevasNonEuclideanOQ01OQ01

open Real Filter Topology
open CevasNonEuclideanOQ01

/-- **Spherical kernel.** The difference quotient `sin(x·t)/t` tends to `x` as `t → 0`
(punctured). This is the slope of `t ↦ sin(x·t)` at `0`, whose derivative there is
`x·cos 0 = x`. -/
theorem tendsto_sin_mul_div (x : ℝ) :
    Tendsto (fun t => Real.sin (x * t) / t) (𝓝[≠] 0) (𝓝 x) := by
  have hd : HasDerivAt (fun t => Real.sin (x * t)) x 0 := by
    have h := (Real.hasDerivAt_sin (x * 0)).comp 0 ((hasDerivAt_id 0).const_mul x)
    simpa using h
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  rw [slope_fun_def_field] at hslope
  refine hslope.congr fun t => ?_
  simp [mul_zero, Real.sin_zero]

/-- **Hyperbolic kernel.** The difference quotient `sinh(x·t)/t` tends to `x` as `t → 0`
(punctured). This is the slope of `t ↦ sinh(x·t)` at `0`, whose derivative there is
`x·cosh 0 = x`. -/
theorem tendsto_sinh_mul_div (x : ℝ) :
    Tendsto (fun t => Real.sinh (x * t) / t) (𝓝[≠] 0) (𝓝 x) := by
  have hd : HasDerivAt (fun t => Real.sinh (x * t)) x 0 := by
    have h := (Real.hasDerivAt_sinh (x * 0)).comp 0 ((hasDerivAt_id 0).const_mul x)
    simpa using h
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  rw [slope_fun_def_field] at hslope
  refine hslope.congr fun t => ?_
  simp [mul_zero, Real.sinh_zero]

/-- `√·` maps the right-punctured neighbourhood of `0` into itself: as `κ → 0⁺`,
`√κ → 0⁺`. -/
theorem sqrt_tendsto_nhdsGT : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
      simpa [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0:ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with κ hκ
    exact Real.sqrt_pos.mpr hκ

/-- As `κ → 0⁻`, `√(−κ) → 0⁺`. -/
theorem sqrt_neg_tendsto_nhdsLT :
    Tendsto (fun κ => Real.sqrt (-κ)) (𝓝[<] (0:ℝ)) (𝓝[>] 0) := by
  have hneg : Tendsto (fun κ : ℝ => -κ) (𝓝[<] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun κ : ℝ => -κ) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg.tendsto (0:ℝ))
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with κ hκ
      have hκ' : κ < 0 := hκ
      exact neg_pos.mpr hκ'
  exact sqrt_tendsto_nhdsGT.comp hneg

/-- The right-punctured neighbourhood of `0` lies below the punctured one. -/
private theorem nhdsGT_le_nhdsNE : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] 0 :=
  nhdsWithin_mono 0 fun _ hy => ne_of_gt hy

/-- **Spherical flat limit.** `sin_κ(x) → x` as the curvature `κ → 0⁺`. -/
theorem tendsto_sinKappa_nhdsGT (x : ℝ) :
    Tendsto (fun κ => sinKappa κ x) (𝓝[>] (0:ℝ)) (𝓝 x) := by
  have hcomp :
      Tendsto (fun κ => Real.sin (x * Real.sqrt κ) / Real.sqrt κ) (𝓝[>] 0) (𝓝 x) :=
    (tendsto_sin_mul_div x).comp (sqrt_tendsto_nhdsGT.mono_right nhdsGT_le_nhdsNE)
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  have hκ' : 0 < κ := hκ
  simp only [sinKappa, if_pos hκ', mul_comm x (Real.sqrt κ)]

/-- **Hyperbolic flat limit.** `sin_κ(x) → x` as the curvature `κ → 0⁻`. -/
theorem tendsto_sinKappa_nhdsLT (x : ℝ) :
    Tendsto (fun κ => sinKappa κ x) (𝓝[<] (0:ℝ)) (𝓝 x) := by
  have hcomp :
      Tendsto (fun κ => Real.sinh (x * Real.sqrt (-κ)) / Real.sqrt (-κ)) (𝓝[<] 0) (𝓝 x) :=
    (tendsto_sinh_mul_div x).comp (sqrt_neg_tendsto_nhdsLT.mono_right nhdsGT_le_nhdsNE)
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  have hκ' : κ < 0 := hκ
  have hκ0 : ¬ (0 : ℝ) < κ := not_lt.mpr (le_of_lt hκ')
  simp only [sinKappa, if_neg hκ0, if_pos hκ', mul_comm x (Real.sqrt (-κ))]

/-- **Punctured two-sided flat limit.** `sin_κ(x) → x` as `κ → 0` with `κ ≠ 0`, gluing the
spherical and hyperbolic branches. -/
theorem tendsto_sinKappa_punctured (x : ℝ) :
    Tendsto (fun κ => sinKappa κ x) (𝓝[≠] (0:ℝ)) (𝓝 x) := by
  rw [← nhdsLT_sup_nhdsGT, tendsto_sup]
  exact ⟨tendsto_sinKappa_nhdsLT x, tendsto_sinKappa_nhdsGT x⟩

/-- **Flat limit (full, two-sided).** `sin_κ(x) → x` as the curvature `κ → 0`. The
curvature sine degenerates continuously to the Euclidean (identity) distance, so the
curvature-`κ` Ceva condition tends to the flat one. -/
theorem tendsto_sinKappa_flat (x : ℝ) :
    Tendsto (fun κ => sinKappa κ x) (𝓝 (0:ℝ)) (𝓝 x) := by
  rw [← nhdsNE_sup_pure, tendsto_sup]
  refine ⟨tendsto_sinKappa_punctured x, ?_⟩
  have : Tendsto (fun κ => sinKappa κ x) (pure 0) (𝓝 (sinKappa 0 x)) :=
    tendsto_pure_nhds _ 0
  rwa [sinKappa_zero] at this

/-- **Ceva ratio degenerates to the Euclidean ratio.** Each curvature-sine ratio
`sin_κ(p) / sin_κ(q)` tends, as `κ → 0`, to the Euclidean ratio `p / q`. Taking the
product over the six sub-segments shows the curvature-`κ` Ceva product tends to the flat
one. -/
theorem sinKappa_ceva_ratio_tendsto (p q : ℝ) (hq : q ≠ 0) :
    Tendsto (fun κ => sinKappa κ p / sinKappa κ q) (𝓝 (0:ℝ)) (𝓝 (p / q)) :=
  (tendsto_sinKappa_flat p).div (tendsto_sinKappa_flat q) hq

end CevasNonEuclideanOQ01OQ01
