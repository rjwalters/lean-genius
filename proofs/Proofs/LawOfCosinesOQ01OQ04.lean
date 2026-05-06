/-
# Small-Angle Limit: Spherical Law of Cosines → Euclidean Law

## Problem: law-of-cosines-oq-01-oq-04

The spherical law of cosines:
  cos(c) = cos(a)·cos(b) + sin(a)·sin(b)·cos(C)

As sides shrink (a = tα, b = tβ, t → 0), the normalized expression
  (1 - cos(tα)·cos(tβ) - sin(tα)·sin(tβ)·cosC) / t²
converges to (α² + β² - 2αβ·cosC)/2.

This is the Euclidean law of cosines: c² = a² + b² - 2ab·cos(C).

Proof uses Taylor remainder bounds:
  1 - cos(tx) = 2sin²(tx/2),  sin(u)/u → 1 as u → 0

References:
- Todhunter, "Spherical Trigonometry" (1886), Chapter III
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

open Real Filter Set

namespace LawOfCosinesSmallAngle

/-! ## Part I: Helper Limits -/

/-- sin(h)/h → 1 as h → 0, h ≠ 0. Follows from sin'(0) = cos(0) = 1. -/
private lemma tendsto_sin_div_zero :
    Tendsto (fun h : ℝ => sin h / h) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hd : HasDerivAt sin 1 0 := by
    have := Real.hasDerivAt_sin 0; rw [Real.cos_zero] at this; exact this
  rw [hasDerivAt_iff_tendsto_slope] at hd
  exact hd.congr' (Eventually.of_forall fun y => by simp [slope_def_field, Real.sin_zero])

/-- sin(t·x)/t → x as t → 0, t ≠ 0.

Proof: d/dt[sin(tx)]|_{t=0} = x·cos(0) = x by the chain rule. -/
lemma tendsto_sin_mul_div (x : ℝ) :
    Tendsto (fun t : ℝ => sin (t * x) / t) (nhdsWithin 0 {0}ᶜ) (nhds x) := by
  have hd : HasDerivAt (fun t : ℝ => sin (t * x)) x 0 := by
    have hf : HasDerivAt (fun t : ℝ => t * x) x 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const x
    have hsin : HasDerivAt Real.sin (Real.cos (0 * x)) (0 * x) :=
      Real.hasDerivAt_sin (0 * x)
    have h := hsin.comp 0 hf
    simp [Function.comp, Real.cos_zero] at h
    exact h
  rw [hasDerivAt_iff_tendsto_slope] at hd
  exact hd.congr' (Eventually.of_forall fun y => by
    simp [slope_def_field, Real.sin_zero])

/-- cos(t·x) → 1 as t → 0. From continuity: cos(0·x) = cos(0) = 1. -/
lemma tendsto_cos_mul (x : ℝ) :
    Tendsto (fun t : ℝ => cos (t * x)) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have h : ContinuousAt (fun t : ℝ => cos (t * x)) 0 :=
    Real.continuous_cos.comp (continuous_id.mul continuous_const) |>.continuousAt
  simp only [ContinuousAt, zero_mul, Real.cos_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- (1 - cos(t·x)) / t² → x²/2 as t → 0, t ≠ 0.

Uses the identity 1 - cos(tx) = 2sin²(tx/2) and the sinc limit sin(u)/u → 1. -/
lemma tendsto_one_sub_cos_div_sq (x : ℝ) :
    Tendsto (fun t : ℝ => (1 - cos (t * x)) / t ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (x ^ 2 / 2)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [tendsto_const_nhds]
  · -- Step 1: Double-angle identity 1 - cos(tx) = 2sin²(tx/2)
    have identity : ∀ t : ℝ, 1 - cos (t * x) = 2 * sin (t * x / 2) ^ 2 := fun t => by
      have h1 := Real.cos_two_mul (t * x / 2)
      have h2 := Real.sin_sq_add_cos_sq (t * x / 2)
      have heq : 2 * (t * x / 2) = t * x := by ring
      linarith [heq ▸ h1]
    -- Step 2: Rewrite (1 - cos(tx))/t² = (x²/2)·(sin(tx/2)/(tx/2))²  for t ≠ 0
    have eq_form : ∀ t : ℝ, t ≠ 0 →
        (1 - cos (t * x)) / t ^ 2 = x ^ 2 / 2 * (sin (t * x / 2) / (t * x / 2)) ^ 2 := by
      intro t ht
      rw [identity t]
      have htx : t * x / 2 ≠ 0 := div_ne_zero (mul_ne_zero ht hx) two_ne_zero
      field_simp [htx]; ring
    -- Step 3: sin(tx/2)/(tx/2) → 1  via t*x/2 → 0 with t*x/2 ≠ 0
    have hinner : Tendsto (fun t : ℝ => t * x / 2) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : ContinuousAt (fun t : ℝ => t * x / 2) 0 :=
          (continuous_id.mul continuous_const |>.div_const 2).continuousAt
        simp only [ContinuousAt, zero_mul, zero_div] at h
        exact h
      · exact Eventually.of_forall fun t ht =>
          mem_compl_singleton_iff.mpr (div_ne_zero (mul_ne_zero (mem_compl_singleton_iff.mp ht) hx) two_ne_zero)
    have sinc_lim : Tendsto (fun t : ℝ => sin (t * x / 2) / (t * x / 2))
                            (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
      tendsto_sin_div_zero.comp hinner
    -- Step 4: Square the sinc limit → (sin(tx/2)/(tx/2))² → 1
    have sinc_sq : Tendsto (fun t : ℝ => (sin (t * x / 2) / (t * x / 2)) ^ 2)
                           (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
      have h := sinc_lim.pow 2; norm_num at h; exact h
    -- Step 5: x²/2 · (sin(tx/2)/(tx/2))² → x²/2
    have prod_lim : Tendsto (fun t : ℝ => x ^ 2 / 2 * (sin (t * x / 2) / (t * x / 2)) ^ 2)
                             (nhdsWithin 0 {0}ᶜ) (nhds (x ^ 2 / 2)) := by
      have h := sinc_sq.const_mul (x ^ 2 / 2)
      simp only [mul_one] at h; exact h
    -- Step 6: Conclude via eq_form
    exact prod_lim.congr' (eventually_nhdsWithin_of_forall fun t ht =>
      (eq_form t (mem_compl_singleton_iff.mp ht)).symm)

/-! ## Part II: Main Theorem -/

/-- **Small-Angle Limit**: The spherical law of cosines expression normalized by t²
converges to the Euclidean law of cosines as t → 0.

Specifically, for fixed α, β, cosC ∈ ℝ:

  lim_{t→0} (1 - cos(tα)·cos(tβ) - sin(tα)·sin(tβ)·cosC) / t²
  = (α² + β² - 2αβ·cosC) / 2

This is the Euclidean law of cosines: setting c² = α² + β² - 2αβ·cosC gives
  2·(limit) = c²  i.e., the spherical formula reduces to the planar one. -/
theorem small_angle_limit (α β cosC : ℝ) :
    Tendsto (fun t : ℝ => (1 - cos (t * α) * cos (t * β) -
                           sin (t * α) * sin (t * β) * cosC) / t ^ 2)
            (nhdsWithin 0 {0}ᶜ)
            (nhds ((α ^ 2 + β ^ 2 - 2 * α * β * cosC) / 2)) := by
  -- Algebraic decomposition for t ≠ 0
  have eq_form : ∀ t : ℝ, t ≠ 0 →
      (1 - cos (t * α) * cos (t * β) - sin (t * α) * sin (t * β) * cosC) / t ^ 2 =
      (1 - cos (t * α)) / t ^ 2 + cos (t * α) * ((1 - cos (t * β)) / t ^ 2) -
      cosC * (sin (t * α) / t) * (sin (t * β) / t) := by
    intro t ht
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht
    field_simp [ht, ht2]; ring
  -- Individual limits
  have hA := tendsto_one_sub_cos_div_sq α
  have hB := tendsto_one_sub_cos_div_sq β
  have hcA := tendsto_cos_mul α
  have hsA := tendsto_sin_mul_div α
  have hsB := tendsto_sin_mul_div β
  -- Combined limit: α²/2 + 1·(β²/2) - cosC·α·β
  have combined : Tendsto
      (fun t : ℝ => (1 - cos (t * α)) / t ^ 2 + cos (t * α) * ((1 - cos (t * β)) / t ^ 2) -
                    cosC * (sin (t * α) / t) * (sin (t * β) / t))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (α ^ 2 / 2 + 1 * (β ^ 2 / 2) - cosC * (α * β))) := by
    apply Tendsto.sub
    · exact hA.add (hcA.mul hB)
    · -- cosC * (sinα/t) * (sinβ/t) → cosC * α * β
      have h := (hsA.mul hsB).const_mul cosC
      exact h.congr' (Eventually.of_forall fun t => by ring)
  -- Limit value simplifies to target
  have heq : α ^ 2 / 2 + 1 * (β ^ 2 / 2) - cosC * (α * β) =
             (α ^ 2 + β ^ 2 - 2 * α * β * cosC) / 2 := by ring
  rw [← heq]
  exact combined.congr' (eventually_nhdsWithin_of_forall fun t ht =>
    (eq_form t (mem_compl_singleton_iff.mp ht)).symm)

/-! ## Part III: Connection to the Spherical Law of Cosines -/

/-- Scaled version: 2·(spherical excess) / t² converges to the Euclidean law value α²+β²-2αβcosC. -/
theorem spherical_to_euclidean_limit (α β cosC : ℝ) :
    Tendsto
      (fun t : ℝ => 2 * (1 - cos (t * α) * cos (t * β) - sin (t * α) * sin (t * β) * cosC) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (α ^ 2 + β ^ 2 - 2 * α * β * cosC)) := by
  have h := (small_angle_limit α β cosC).const_mul 2
  have key : (2 : ℝ) * ((α ^ 2 + β ^ 2 - 2 * α * β * cosC) / 2) =
             α ^ 2 + β ^ 2 - 2 * α * β * cosC := by ring
  rw [← key]
  exact h.congr' (Eventually.of_forall fun t => by ring)

/-! ## Part IV: Concrete Verifications -/

/-- For a right triangle (cosC = 0), the limit gives (α² + β²)/2:
    Pythagorean theorem in the small-angle limit. -/
example : Filter.Tendsto
    (fun t : ℝ => (1 - cos (t * 3) * cos (t * 4) - sin (t * 3) * sin (t * 4) * 0) / t ^ 2)
    (nhdsWithin 0 {0}ᶜ) (nhds (25 / 2)) := by
  have h := small_angle_limit 3 4 0
  norm_num at h ⊢; exact h

/-- For an equilateral triangle (α = β, cosC = 1/2), the limit gives α²/2:
    The formula gives (α² + α² - 2α²·(1/2))/2 = α²/2. -/
example (α : ℝ) : Filter.Tendsto
    (fun t : ℝ => (1 - cos (t * α) * cos (t * α) - sin (t * α) * sin (t * α) * (1/2)) / t ^ 2)
    (nhdsWithin 0 {0}ᶜ) (nhds (α ^ 2 / 2)) := by
  have h := small_angle_limit α α (1/2)
  convert h using 2; ring

end LawOfCosinesSmallAngle
