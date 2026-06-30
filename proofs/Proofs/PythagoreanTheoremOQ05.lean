/-
# Pythagorean Theorem OQ-05: Flat-Limit Reduction

## What This Proves

Both non-Euclidean Pythagorean theorems reduce to the Euclidean form c² = a² + b²
as curvature → 0. Specifically:

- **Hyperbolic**: If cosh(t·c) = cosh(t·a)·cosh(t·b) for all t > 0, then c² = a² + b².
- **Spherical**: If cos(t·c) = cos(t·a)·cos(t·b) for all small t > 0, then c² = a² + b².

## Proof Strategy

The flat limit is proved via the squeeze theorem for the limit:
  (cosh(t·x) - 1) / t² → x² / 2  as  t → 0⁺

Key bounds for any x : ℝ and t > 0:
- **Lower**: cosh(tx) ≥ 1 + (tx)²/2  →  (cosh(tx)-1)/t² ≥ x²/2
- **Upper**: 2·(cosh(tx)-1) ≤ (tx)²·cosh(tx)  →  (cosh(tx)-1)/t² ≤ x²·cosh(tx)/2

The upper bound `2(cosh u - 1) ≤ u²·cosh u` is proved by a two-level monotonicity
argument: the second derivative of `u²·cosh u - 2(cosh u - 1)` equals
`u²·cosh u + 4u·sinh u ≥ 0` for u ≥ 0.

The product limit (cosh(ta)·cosh(tb)-1)/t² → (a²+b²)/2 follows by decomposing:
  (cosh(ta)·cosh(tb) - 1)/t² = (cosh(ta)-1)/t² · cosh(tb) + (cosh(tb)-1)/t²
and using continuity of cosh at 0.

## Status: 0 sorries, 0 axioms (both hyperbolic and spherical cases fully proved)

Tags: geometry, non-euclidean, flat-limit, taylor-approximation, squeeze-theorem
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

open Real Filter Set
open scoped Topology

namespace PythagoreanFlatLimit

-- ============================================================
-- Part I: Derivatives of cosh and sinh
-- ============================================================

/-- HasDerivAt for cosh: cosh'(x) = sinh(x). -/
theorem hasDerivAt_cosh' (x : ℝ) : HasDerivAt Real.cosh (Real.sinh x) x := by
  have h1 := Real.hasDerivAt_exp x
  have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hcoshDef : Real.cosh = fun y => (Real.exp y + Real.exp (-y)) / 2 :=
    funext Real.cosh_eq
  rw [hcoshDef]
  have hsinhEq : Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := Real.sinh_eq x
  rw [hsinhEq]
  have := (h1.add h2).div_const 2
  convert this using 1; ring

/-- HasDerivAt for sinh: sinh'(x) = cosh(x). -/
theorem hasDerivAt_sinh' (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x := by
  have h1 := Real.hasDerivAt_exp x
  have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hsinhDef : Real.sinh = fun y => (Real.exp y - Real.exp (-y)) / 2 :=
    funext Real.sinh_eq
  rw [hsinhDef]
  have hcoshEq : Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := Real.cosh_eq x
  rw [hcoshEq]
  have := (h1.sub h2).div_const 2
  convert this using 1; ring

-- ============================================================
-- Part II: Basic inequalities
-- ============================================================

/-- cosh(x) > 0 for all x. -/
theorem cosh_pos' (x : ℝ) : 0 < Real.cosh x := by
  rw [Real.cosh_eq]; positivity

/-- cosh(x) ≥ 1 for all x. -/
theorem cosh_ge_one' (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have := Real.add_one_le_exp x
  have := Real.add_one_le_exp (-x)
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- sinh(x) ≥ x for x ≥ 0 (super-linearity from cosh ≥ 1). -/
theorem sinh_ge_id' (x : ℝ) (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  suffices h : Real.sinh x - x ≥ 0 by linarith
  let f : ℝ → ℝ := fun y => Real.sinh y - y
  have hf0 : f 0 = 0 := by show Real.sinh 0 - 0 = 0; norm_num [Real.sinh_zero]
  have hf_cont : ContinuousOn f (Icc 0 x) :=
    (Real.continuous_sinh.sub continuous_id).continuousOn
  have hf_diff : DifferentiableOn ℝ f (interior (Icc 0 x)) := by
    intro t _
    exact ((hasDerivAt_sinh' t).sub (hasDerivAt_id t)).differentiableAt.differentiableWithinAt
  have hf_deriv : ∀ t ∈ interior (Icc 0 x), 0 ≤ deriv f t := by
    intro t ht
    have hd : HasDerivAt f (Real.cosh t - 1) t :=
      (hasDerivAt_sinh' t).sub (hasDerivAt_id t)
    rw [hd.deriv]; linarith [cosh_ge_one' t]
  have hf_mono : MonotoneOn f (Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hf_cont hf_diff hf_deriv
  have := hf_mono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  rw [hf0] at this; exact this

/-- cosh(x) ≥ 1 + x²/2 for x ≥ 0. -/
theorem cosh_ge_one_add_sq_div_two' (x : ℝ) (hx : 0 ≤ x) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  suffices h : Real.cosh x - 1 - x ^ 2 / 2 ≥ 0 by linarith
  let f : ℝ → ℝ := fun y => Real.cosh y - 1 - y ^ 2 / 2
  have hf0 : f 0 = 0 := by show Real.cosh 0 - 1 - 0 ^ 2 / 2 = 0; norm_num [Real.cosh_zero]
  have hf_cont : ContinuousOn f (Icc 0 x) := by
    exact (Real.continuous_cosh.sub continuous_const |>.sub
      ((continuous_pow 2).div_const 2)).continuousOn
  have hf_diff : DifferentiableOn ℝ f (interior (Icc 0 x)) := by
    intro t _
    have : HasDerivAt f (Real.sinh t - t) t := by
      have hd3 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
        convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
      have hcomb : HasDerivAt f (Real.sinh t - 0 - t) t :=
        ((hasDerivAt_cosh' t).sub (hasDerivAt_const t 1)).sub hd3
      simpa using hcomb
    exact this.differentiableAt.differentiableWithinAt
  have hf_deriv : ∀ t ∈ interior (Icc 0 x), 0 ≤ deriv f t := by
    intro t ht
    have hd3 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1; ring
    have hd : HasDerivAt f (Real.sinh t - t) t := by
      have hcomb : HasDerivAt f (Real.sinh t - 0 - t) t :=
        ((hasDerivAt_cosh' t).sub (hasDerivAt_const t 1)).sub hd3
      simpa using hcomb
    rw [hd.deriv]; linarith [sinh_ge_id' t (interior_subset ht).1]
  have hf_mono : MonotoneOn f (Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hf_cont hf_diff hf_deriv
  have := hf_mono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  rw [hf0] at this; exact this

/-- cosh(x) ≥ 1 + x²/2 for all real x (extend via evenness). -/
theorem cosh_ge_one_add_sq_div_two_all (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  rcases le_or_gt 0 x with hx | hx
  · exact cosh_ge_one_add_sq_div_two' x hx
  · have h := cosh_ge_one_add_sq_div_two' (-x) (by linarith)
    rwa [Real.cosh_neg, neg_sq] at h

-- ============================================================
-- Part III: Upper bound 2·(cosh u - 1) ≤ u²·cosh u
-- Two-level monotonicity argument
-- ============================================================

/-- First derivative of g(u) = u²·cosh u - 2(cosh u - 1):
    g'(u) = 2u·cosh u + (u²-2)·sinh u. -/
private noncomputable def gDeriv (u : ℝ) : ℝ :=
  2 * u * Real.cosh u + (u ^ 2 - 2) * Real.sinh u

private theorem gDeriv_zero : gDeriv 0 = 0 := by
  simp [gDeriv, Real.cosh_zero, Real.sinh_zero]

private theorem hasDerivAt_gFun (u : ℝ) :
    HasDerivAt (fun u => u ^ 2 * Real.cosh u - 2 * (Real.cosh u - 1)) (gDeriv u) u := by
  unfold gDeriv
  have hc := hasDerivAt_cosh' u
  have hs := hasDerivAt_sinh' u
  have ht2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    convert (hasDerivAt_pow 2 u) using 1; norm_cast; ring
  -- d/dt[u²·cosh u] = 2u·cosh u + u²·sinh u
  have h1 : HasDerivAt (fun u => u ^ 2 * Real.cosh u) (2 * u * Real.cosh u + u ^ 2 * Real.sinh u) u :=
    ht2.mul hc |>.congr_deriv (by ring)
  -- d/dt[-2(cosh u - 1)] = -2·sinh u
  have h2 : HasDerivAt (fun u => 2 * (Real.cosh u - 1)) (2 * Real.sinh u) u := by
    have := (hc.sub (hasDerivAt_const u 1)).const_mul 2
    convert this using 1; ring
  have := h1.sub h2
  convert this using 1; ring

/-- HasDerivAt for gDeriv (second derivative of g):
    g''(u) = u²·cosh u + 4u·sinh u. -/
private theorem hasDerivAt_gDeriv (u : ℝ) :
    HasDerivAt gDeriv (u ^ 2 * Real.cosh u + 4 * u * Real.sinh u) u := by
  unfold gDeriv
  have hc := hasDerivAt_cosh' u
  have hs := hasDerivAt_sinh' u
  have ht2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    convert (hasDerivAt_pow 2 u) using 1; norm_cast; ring
  -- d/du[2u·cosh u] = 2·cosh u + 2u·sinh u
  have h1 : HasDerivAt (fun u => 2 * u * Real.cosh u) (2 * Real.cosh u + 2 * u * Real.sinh u) u := by
    have := (hasDerivAt_id u |>.const_mul 2).mul hc
    convert this using 1; simp only [id_eq]; ring
  -- d/du[(u²-2)·sinh u] = 2u·sinh u + (u²-2)·cosh u
  have h2 : HasDerivAt (fun u => (u ^ 2 - 2) * Real.sinh u)
      (2 * u * Real.sinh u + (u ^ 2 - 2) * Real.cosh u) u := by
    have hd : HasDerivAt (fun u : ℝ => u ^ 2 - 2) (2 * u) u := by
      convert ht2.sub (hasDerivAt_const u 2) using 1; ring
    have := hd.mul hs
    convert this using 1
  have := h1.add h2
  convert this using 1; ring

/-- g''(u) = u²·cosh u + 4u·sinh u ≥ 0 for u ≥ 0. -/
private theorem gSecondDeriv_nonneg (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ u ^ 2 * Real.cosh u + 4 * u * Real.sinh u := by
  have h1 : 0 ≤ u ^ 2 * Real.cosh u := mul_nonneg (sq_nonneg u) (cosh_pos' u).le
  have h2 : 0 ≤ 4 * u * Real.sinh u :=
    mul_nonneg (mul_nonneg (by norm_num) hu) (by linarith [sinh_ge_id' u hu])
  linarith

/-- gDeriv(u) ≥ 0 for u ≥ 0: apply monotoneOn to gDeriv itself. -/
private theorem gDeriv_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ gDeriv x := by
  suffices hg : gDeriv 0 ≤ gDeriv x by rwa [gDeriv_zero] at hg
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
  · -- ContinuousOn gDeriv [0, x]
    unfold gDeriv
    exact ((continuous_const.mul continuous_id |>.mul Real.continuous_cosh).add
      ((continuous_pow 2 |>.sub continuous_const).mul Real.continuous_sinh)).continuousOn
  · -- DifferentiableOn gDeriv on interior
    intro u _
    exact (hasDerivAt_gDeriv u).differentiableAt.differentiableWithinAt
  · -- deriv gDeriv ≥ 0
    intro u hu
    rw [(hasDerivAt_gDeriv u).deriv]
    exact gSecondDeriv_nonneg u (interior_subset hu).1
  · exact Set.left_mem_Icc.mpr hx
  · exact Set.right_mem_Icc.mpr hx
  · exact hx

/-- Key upper bound: 2·(cosh u - 1) ≤ u²·cosh u for u ≥ 0. -/
theorem cosh_sub_one_le_sq_mul_cosh (u : ℝ) (hu : 0 ≤ u) :
    2 * (Real.cosh u - 1) ≤ u ^ 2 * Real.cosh u := by
  have hmono : MonotoneOn (fun v => v ^ 2 * Real.cosh v - 2 * (Real.cosh v - 1)) (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
    · exact ((continuous_pow 2 |>.mul Real.continuous_cosh).sub
        (continuous_const.mul (Real.continuous_cosh.sub continuous_const))).continuousOn
    · intro v _
      exact (hasDerivAt_gFun v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [(hasDerivAt_gFun v).deriv]
      exact gDeriv_nonneg v (interior_subset hv).1
  have key := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  simp only [Real.cosh_zero] at key
  nlinarith [key]

/-- Upper bound for all real u (via evenness of cosh). -/
theorem cosh_sub_one_le_sq_mul_cosh_all (u : ℝ) : 2 * (Real.cosh u - 1) ≤ u ^ 2 * Real.cosh u := by
  rcases le_or_gt 0 u with hu | hu
  · exact cosh_sub_one_le_sq_mul_cosh u hu
  · have h := cosh_sub_one_le_sq_mul_cosh (-u) (by linarith)
    rwa [Real.cosh_neg, neg_sq] at h

-- ============================================================
-- Part IV: The scaled limit (cosh(tx)-1)/t² → x²/2 as t → 0⁺
-- Proved by squeeze for each x : ℝ
-- ============================================================

/-- Squeeze bounds for (cosh(tx)-1)/t²: x²/2 ≤ (cosh(tx)-1)/t² ≤ x²·cosh(tx)/2. -/
theorem cosh_mul_sub_one_div_sq_bounds (x : ℝ) (t : ℝ) (ht : 0 < t) :
    x ^ 2 / 2 ≤ (Real.cosh (t * x) - 1) / t ^ 2 ∧
    (Real.cosh (t * x) - 1) / t ^ 2 ≤ x ^ 2 * Real.cosh (t * x) / 2 := by
  have ht2 : (0 : ℝ) < t ^ 2 := sq_pos_of_pos ht
  constructor
  · rw [le_div_iff₀ ht2]
    have h := cosh_ge_one_add_sq_div_two_all (t * x)
    nlinarith [sq_nonneg (t * x)]
  · rw [div_le_div_iff₀ ht2 two_pos]
    have h := cosh_sub_one_le_sq_mul_cosh_all (t * x)
    nlinarith [sq_abs (t * x), sq_nonneg t, sq_nonneg x]

/-- The flat-limit for scaled cosh: (cosh(tx)-1)/t² → x²/2 as t → 0⁺. -/
theorem tendsto_cosh_mul_sub_one_div_sq (x : ℝ) :
    Tendsto (fun t : ℝ => (Real.cosh (t * x) - 1) / t ^ 2) (𝓝[Ioi 0] 0) (𝓝 (x ^ 2 / 2)) := by
  -- Upper bounding function x²·cosh(tx)/2 → x²/2 by continuity of cosh at 0
  have hcont : Tendsto (fun t : ℝ => x ^ 2 * Real.cosh (t * x) / 2)
      (𝓝[Ioi 0] 0) (𝓝 (x ^ 2 / 2)) := by
    have hcosh : Tendsto (fun t : ℝ => Real.cosh (t * x)) (𝓝[Ioi 0] 0) (𝓝 1) := by
      have : Tendsto (fun t : ℝ => Real.cosh (t * x)) (𝓝 0) (𝓝 (Real.cosh (0 * x))) :=
        Real.continuous_cosh.continuousAt.comp (continuous_id.mul continuous_const).continuousAt
      simp only [zero_mul, Real.cosh_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h := (hcosh.const_mul (x ^ 2)).div_const 2
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcont ?_ ?_
  · exact eventually_nhdsWithin_of_forall fun t ht => (cosh_mul_sub_one_div_sq_bounds x t ht).1
  · exact eventually_nhdsWithin_of_forall fun t ht => (cosh_mul_sub_one_div_sq_bounds x t ht).2

-- ============================================================
-- Part V: Product limit (cosh(ta)·cosh(tb)-1)/t² → (a²+b²)/2
-- ============================================================

/-- cosh(tx) → 1 as t → 0⁺ (continuity). -/
theorem tendsto_cosh_mul_one (x : ℝ) :
    Tendsto (fun t : ℝ => Real.cosh (t * x)) (𝓝[Ioi 0] 0) (𝓝 1) := by
  have : Tendsto (fun t : ℝ => Real.cosh (t * x)) (𝓝 0) (𝓝 (Real.cosh (0 * x))) :=
    Real.continuous_cosh.continuousAt.comp (continuous_id.mul continuous_const).continuousAt
  simp only [zero_mul, Real.cosh_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The product limit: (cosh(ta)·cosh(tb)-1)/t² → (a²+b²)/2 as t → 0⁺.
    Uses decomposition: (cosh(ta)·cosh(tb)-1)/t² = (cosh(ta)-1)/t²·cosh(tb) + (cosh(tb)-1)/t². -/
theorem tendsto_cosh_prod_sub_one_div_sq (a b : ℝ) :
    Tendsto (fun t : ℝ => (Real.cosh (t * a) * Real.cosh (t * b) - 1) / t ^ 2)
    (𝓝[Ioi 0] 0) (𝓝 ((a ^ 2 + b ^ 2) / 2)) := by
  -- Algebraic identity for t ≠ 0:
  -- (cosh(ta)·cosh(tb)-1)/t² = (cosh(ta)-1)/t²·cosh(tb) + (cosh(tb)-1)/t²
  have heq : ∀ t : ℝ, t ∈ Ioi (0:ℝ) →
      (Real.cosh (t * a) * Real.cosh (t * b) - 1) / t ^ 2 =
      (Real.cosh (t * a) - 1) / t ^ 2 * Real.cosh (t * b) + (Real.cosh (t * b) - 1) / t ^ 2 := by
    intro t ht
    have ht2 : t ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos ht)
    field_simp; ring
  rw [show (a ^ 2 + b ^ 2) / 2 = a ^ 2 / 2 * 1 + b ^ 2 / 2 by ring]
  apply Tendsto.congr'
  · exact eventually_nhdsWithin_of_forall fun t ht => (heq t ht).symm
  · exact ((tendsto_cosh_mul_sub_one_div_sq a).mul (tendsto_cosh_mul_one b)).add
      (tendsto_cosh_mul_sub_one_div_sq b)

-- ============================================================
-- Part VI: Main Flat-Limit Theorems
-- ============================================================

/-- **Hyperbolic Flat Limit**: If cosh(t·c) = cosh(t·a)·cosh(t·b) for all t > 0,
    then c² = a² + b².

    This is the mathematical core of the flat limit: the hyperbolic Pythagorean theorem
    (which holds in negatively curved space) reduces to the Euclidean theorem as the
    curvature κ → 0 (equivalently, side lengths shrink relative to the curvature radius). -/
theorem hyperbolic_flat_limit {a b c : ℝ}
    (h : ∀ t : ℝ, 0 < t → Real.cosh (t * c) = Real.cosh (t * a) * Real.cosh (t * b)) :
    c ^ 2 = a ^ 2 + b ^ 2 := by
  have hlhs : Tendsto (fun t : ℝ => (Real.cosh (t * c) - 1) / t ^ 2) (𝓝[Ioi 0] 0) (𝓝 (c ^ 2 / 2)) :=
    tendsto_cosh_mul_sub_one_div_sq c
  have hrhs : Tendsto (fun t : ℝ => (Real.cosh (t * a) * Real.cosh (t * b) - 1) / t ^ 2)
      (𝓝[Ioi 0] 0) (𝓝 ((a ^ 2 + b ^ 2) / 2)) :=
    tendsto_cosh_prod_sub_one_div_sq a b
  -- On (0,∞), the two functions agree (from hypothesis h)
  have hagree : ∀ᶠ t in 𝓝[Ioi 0] 0,
      (Real.cosh (t * c) - 1) / t ^ 2 = (Real.cosh (t * a) * Real.cosh (t * b) - 1) / t ^ 2 :=
    eventually_nhdsWithin_of_forall fun t ht => by rw [h t ht]
  -- By uniqueness of limits: c²/2 = (a²+b²)/2
  have : c ^ 2 / 2 = (a ^ 2 + b ^ 2) / 2 :=
    tendsto_nhds_unique (hlhs.congr' hagree) hrhs
  linarith

-- ============================================================
-- Part Va: Spherical scaled limit (1 - cos(tx))/t² → x²/2
-- Proved via the exact identity (1 - cos(tx))/t² = (x²/2)·sinc(tx/2)²
-- ============================================================

/-- `sin u = sinc u · u` for all real `u` (sinc absorbs the removable singularity). -/
theorem sin_eq_sinc_mul (u : ℝ) : Real.sin u = Real.sinc u * u := by
  rcases eq_or_ne u 0 with h | h
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]; field_simp

/-- The spherical flat-limit for scaled cos: `(1 - cos(tx))/t² → x²/2` as `t → 0⁺`.

    The mechanism is the exact algebraic identity (for `t ≠ 0`)
      `(1 - cos(tx))/t² = (x²/2)·sinc(tx/2)²`,
    obtained from the half-angle identity `1 - cos(tx) = 2 sin(tx/2)²` and
    `sin u = sinc u · u`. Since `sinc` is continuous with `sinc 0 = 1`, the
    right-hand side tends to `x²/2`. This is the spherical analogue of
    `tendsto_cosh_mul_sub_one_div_sq`. -/
theorem tendsto_one_sub_cos_mul_div_sq (x : ℝ) :
    Tendsto (fun t : ℝ => (1 - Real.cos (t * x)) / t ^ 2) (𝓝[Ioi 0] 0) (𝓝 (x ^ 2 / 2)) := by
  -- Exact identity on (0,∞): (1-cos(tx))/t² = (x²/2)·sinc(tx/2)²
  have heq : ∀ t : ℝ, t ∈ Ioi (0:ℝ) →
      (1 - Real.cos (t * x)) / t ^ 2 = x ^ 2 / 2 * Real.sinc (t * x / 2) ^ 2 := by
    intro t ht
    have ht2 : t ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos ht)
    -- half-angle: 1 - cos(tx) = 2·sin(tx/2)²
    have hcos2 := Real.cos_two_mul (t * x / 2)
    rw [show (2:ℝ) * (t * x / 2) = t * x by ring] at hcos2
    have hpyth := Real.sin_sq_add_cos_sq (t * x / 2)
    have half : 1 - Real.cos (t * x) = 2 * Real.sin (t * x / 2) ^ 2 := by linarith
    rw [half, sin_eq_sinc_mul (t * x / 2), div_eq_iff ht2]; ring
  -- t·x/2 → 0, hence sinc(t·x/2) → sinc 0 = 1
  have htto : Tendsto (fun t : ℝ => t * x / 2) (𝓝[Ioi 0] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t * x / 2) (𝓝 0) (𝓝 (0 * x / 2)) :=
      ((continuous_id.mul continuous_const).div_const 2).continuousAt.tendsto
    simp only [zero_mul, zero_div] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hsinc : Tendsto (fun t : ℝ => Real.sinc (t * x / 2)) (𝓝[Ioi 0] 0) (𝓝 1) := by
    have hc : Tendsto Real.sinc (𝓝 (0:ℝ)) (𝓝 (Real.sinc 0)) := Real.continuous_sinc.continuousAt
    rw [Real.sinc_zero] at hc
    exact hc.comp htto
  rw [show x ^ 2 / 2 = x ^ 2 / 2 * 1 ^ 2 by ring]
  apply Tendsto.congr'
  · exact eventually_nhdsWithin_of_forall fun t ht => (heq t ht).symm
  · exact (hsinc.pow 2).const_mul (x ^ 2 / 2)

/-- cos(tx) → 1 as t → 0⁺ (continuity). -/
theorem tendsto_cos_mul_one (x : ℝ) :
    Tendsto (fun t : ℝ => Real.cos (t * x)) (𝓝[Ioi 0] 0) (𝓝 1) := by
  have : Tendsto (fun t : ℝ => Real.cos (t * x)) (𝓝 0) (𝓝 (Real.cos (0 * x))) :=
    Real.continuous_cos.continuousAt.comp (continuous_id.mul continuous_const).continuousAt
  simp only [zero_mul, Real.cos_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The spherical product limit: `(1 - cos(ta)·cos(tb))/t² → (a²+b²)/2` as `t → 0⁺`.
    Uses the decomposition
      `(1 - cos(ta)·cos(tb))/t² = (1-cos(ta))/t²·cos(tb) + (1-cos(tb))/t²`. -/
theorem tendsto_one_sub_cos_prod_div_sq (a b : ℝ) :
    Tendsto (fun t : ℝ => (1 - Real.cos (t * a) * Real.cos (t * b)) / t ^ 2)
    (𝓝[Ioi 0] 0) (𝓝 ((a ^ 2 + b ^ 2) / 2)) := by
  have heq : ∀ t : ℝ, t ∈ Ioi (0:ℝ) →
      (1 - Real.cos (t * a) * Real.cos (t * b)) / t ^ 2 =
      (1 - Real.cos (t * a)) / t ^ 2 * Real.cos (t * b) + (1 - Real.cos (t * b)) / t ^ 2 := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp; ring
  rw [show (a ^ 2 + b ^ 2) / 2 = a ^ 2 / 2 * 1 + b ^ 2 / 2 by ring]
  apply Tendsto.congr'
  · exact eventually_nhdsWithin_of_forall fun t ht => (heq t ht).symm
  · exact ((tendsto_one_sub_cos_mul_div_sq a).mul (tendsto_cos_mul_one b)).add
      (tendsto_one_sub_cos_mul_div_sq b)

/-- **Spherical Flat Limit**: If cos(t·c) = cos(t·a)·cos(t·b) for all t > 0,
    then c² = a² + b².

    The spherical Pythagorean theorem (positive curvature) also reduces to the Euclidean
    theorem as curvature → 0. No range restriction on a, b, c is needed: the flat limit
    extracts the second-order (t → 0⁺) behaviour, where the spherical law of cosines
    `cos c = cos a · cos b` linearizes to `c² = a² + b²`. This mirrors `hyperbolic_flat_limit`. -/
theorem spherical_flat_limit {a b c : ℝ}
    (h : ∀ t : ℝ, 0 < t → Real.cos (t * c) = Real.cos (t * a) * Real.cos (t * b)) :
    c ^ 2 = a ^ 2 + b ^ 2 := by
  have hlhs : Tendsto (fun t : ℝ => (1 - Real.cos (t * c)) / t ^ 2)
      (𝓝[Ioi 0] 0) (𝓝 (c ^ 2 / 2)) :=
    tendsto_one_sub_cos_mul_div_sq c
  have hrhs : Tendsto (fun t : ℝ => (1 - Real.cos (t * a) * Real.cos (t * b)) / t ^ 2)
      (𝓝[Ioi 0] 0) (𝓝 ((a ^ 2 + b ^ 2) / 2)) :=
    tendsto_one_sub_cos_prod_div_sq a b
  -- On (0,∞), the two functions agree (from hypothesis h)
  have hagree : ∀ᶠ t in 𝓝[Ioi 0] 0,
      (1 - Real.cos (t * c)) / t ^ 2 =
      (1 - Real.cos (t * a) * Real.cos (t * b)) / t ^ 2 :=
    eventually_nhdsWithin_of_forall fun t ht => by rw [h t ht]
  -- By uniqueness of limits: c²/2 = (a²+b²)/2
  have : c ^ 2 / 2 = (a ^ 2 + b ^ 2) / 2 :=
    tendsto_nhds_unique (hlhs.congr' hagree) hrhs
  linarith

end PythagoreanFlatLimit
