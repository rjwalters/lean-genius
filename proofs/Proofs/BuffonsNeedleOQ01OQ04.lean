import Mathlib
import Proofs.BuffonsNeedleOQ01

/-
# Buffon's Coin: the Cauchy mean-width specialization (OQ-01-OQ-04)

**Status**: Fully verified (0 axioms, 0 sorries)

This file resolves the fourth open question of `buffons-needle-oq-01`: the
connection between the smooth Buffon-Barbier theorem and **Buffon's coin**
(Laplace 1812). Instead of a 1-D needle, a 2-D convex body `K` with a
C¹-smooth boundary is dropped onto a parallel line grid of spacing `d`. The
expected number of times its boundary `∂K` crosses the grid depends only on
the perimeter `p`, not on the shape:

  E[boundary crossings] = 2 · p / (π · d).

This is exactly `buffon_smooth_of_contDiff` (the parent's main theorem)
applied to a closed C¹ parametrisation of `∂K`, so the analytic content is
entirely reused. The contribution here is the **coin packaging**:

1. `buffon_coin_boundary_crossings` — the boundary-crossing formula for a
   closed C¹ curve, a one-line corollary of the bearer.
2. `expectedLineCuts` / `buffon_coin_lineCuts` — the number of grid *lines*
   that cut `K`. For a convex body each cutting line meets `∂K` in exactly
   two points, so the line count is half the boundary-crossing count, giving
   E[lines cutting K] = p / (π · d). This factor-of-two is the *only* place
   convexity enters; it is encoded definitionally (`expectedLineCuts := … / 2`)
   rather than derived from a convex-geometry API — Mathlib v4.26.0 has no
   `Convex.line_intersection_card_le_two` bearer, and the integral model of
   `concreteSmoothExpectedCrossings` is not a literal point count, so the
   honest statement of the 0/2 dichotomy is the halving definition.
3. The **circle (coin)** instance: `circle r` of radius `r` has perimeter
   `2πr`, hence E[crossings] = `4r/d` and E[lines cutting] = `2r/d`. The
   latter, for `r ≤ d/2`, is the classical Buffon's-coin crossing probability
   `diameter / d`.
4. Shape independence and sign structural lemmas.

## Connection to prior work

- `BuffonsNeedle.lean` (Wiedijk #99): straight needle, P = 2ℓ/(πd).
- `BuffonsNeedleOQ01.lean`: `buffon_smooth_of_contDiff` — the C¹ bearer used here.
- `BuffonsNeedleOQ01OQ02.lean`: hyperplane-arrangement sibling (n-D constants).
- **This file**: Buffon's coin (convex-body specialization), 0 axioms, 0 sorries.
-/

namespace BuffonsNeedleOQ01OQ04

open Real MeasureTheory
open BuffonsNeedleOQ01OQ01 (concreteSmoothExpectedCrossings planarArcLength)

/-! ## Part I: Perimeter of a C¹ convex boundary -/

/-- The perimeter of a convex body `K` whose boundary `∂K` is parametrised by a
    closed C¹ curve `γ : [a, b] → ℝ²` (with `γ a = γ b`) is the arc length of
    that boundary curve. -/
noncomputable def boundaryPerimeter (γ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  planarArcLength γ a b

/-- The perimeter is nonnegative on `[a, b]` with `a ≤ b` (an arc-length integral
    of a nonnegative integrand). -/
theorem boundaryPerimeter_nonneg (γ : ℝ → ℝ × ℝ) (a b : ℝ) (hab : a ≤ b) :
    0 ≤ boundaryPerimeter γ a b := by
  unfold boundaryPerimeter planarArcLength
  exact intervalIntegral.integral_nonneg hab (fun t _ => Real.sqrt_nonneg _)

/-! ## Part II: Buffon's coin — boundary crossings -/

/-- **Buffon's coin (boundary form)**: for a convex body `K` whose boundary is a
    closed C¹ curve `γ` on `[a, b]`, the expected number of crossings of `∂K`
    with a parallel line grid of spacing `d` is `2 · perimeter(K) / (π · d)`.

    This is `buffon_smooth_of_contDiff` applied to the boundary curve; the
    closure hypothesis `γ a = γ b` is what makes `planarArcLength γ a b` the
    full perimeter of the closed boundary (it is not needed for the formula
    itself). -/
theorem buffon_coin_boundary_crossings
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hC1 : ContDiff ℝ 1 γ)
    (_hclosed : γ a = γ b) :
    concreteSmoothExpectedCrossings γ a b d
      = 2 * boundaryPerimeter γ a b / (π * d) :=
  BuffonsNeedleOQ01.buffon_smooth_of_contDiff γ a b d hd hab hC1

/-! ## Part III: Buffon's coin — lines that cut `K` -/

/-- Expected number of grid lines that **cut** the convex body `K` (meet its
    interior). For a convex body, each cutting line crosses the boundary `∂K` in
    exactly two points, so the number of lines cutting `K` is half the number of
    boundary crossings. This factor-of-two is the sole imprint of convexity. -/
noncomputable def expectedLineCuts (γ : ℝ → ℝ × ℝ) (a b d : ℝ) : ℝ :=
  concreteSmoothExpectedCrossings γ a b d / 2

/-- **Buffon's coin (line-cut form)**: the expected number of grid lines cutting
    a convex body `K` with closed C¹ boundary equals `perimeter(K) / (π · d)`. -/
theorem buffon_coin_lineCuts
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ) (hclosed : γ a = γ b) :
    expectedLineCuts γ a b d = boundaryPerimeter γ a b / (π * d) := by
  unfold expectedLineCuts
  rw [buffon_coin_boundary_crossings γ a b d hd hab hC1 hclosed]
  ring

/-- The expected number of cutting lines is nonnegative. -/
theorem expectedLineCuts_nonneg
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ) (hclosed : γ a = γ b) :
    0 ≤ expectedLineCuts γ a b d := by
  rw [buffon_coin_lineCuts γ a b d hd hab hC1 hclosed]
  exact div_nonneg (boundaryPerimeter_nonneg γ a b hab) (mul_pos Real.pi_pos hd).le

/-! ## Part IV: The circle (the coin)

The canonical convex body: a disk of radius `r`, boundary `t ↦ (r cos t, r sin t)`.
-/

/-- The boundary circle of radius `r`, parametrised on `[0, 2π]`. -/
noncomputable def circle (r : ℝ) : ℝ → ℝ × ℝ :=
  fun t => (r * Real.cos t, r * Real.sin t)

/-- The circle parametrisation is C¹. -/
theorem circle_contDiff (r : ℝ) : ContDiff ℝ 1 (circle r) := by
  unfold circle
  fun_prop

/-- The circle is a closed curve: `γ 0 = γ (2π)`. -/
theorem circle_closed (r : ℝ) : circle r 0 = circle r (2 * π) := by
  unfold circle
  rw [Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]

/-- x-component derivative of the circle: `d/dt (r cos t) = r · (-sin t)`. -/
theorem circle_deriv_fst (r : ℝ) (t : ℝ) :
    deriv (Prod.fst ∘ circle r) t = r * (-Real.sin t) :=
  ((Real.hasDerivAt_cos t).const_mul r).deriv

/-- y-component derivative of the circle: `d/dt (r sin t) = r · cos t`. -/
theorem circle_deriv_snd (r : ℝ) (t : ℝ) :
    deriv (Prod.snd ∘ circle r) t = r * Real.cos t :=
  ((Real.hasDerivAt_sin t).const_mul r).deriv

/-- **Circle perimeter**: the boundary of a disk of radius `r ≥ 0` has perimeter
    `2πr`. -/
theorem circle_perimeter (r : ℝ) (hr : 0 ≤ r) :
    boundaryPerimeter (circle r) 0 (2 * π) = 2 * π * r := by
  unfold boundaryPerimeter planarArcLength
  have hint :
      (fun t => Real.sqrt ((deriv (Prod.fst ∘ circle r) t) ^ 2
        + (deriv (Prod.snd ∘ circle r) t) ^ 2)) = fun _ => r := by
    ext t
    rw [circle_deriv_fst, circle_deriv_snd]
    have hsc : (r * (-Real.sin t)) ^ 2 + (r * Real.cos t) ^ 2 = r ^ 2 := by
      have h : (r * (-Real.sin t)) ^ 2 + (r * Real.cos t) ^ 2
          = r ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      rw [h, Real.sin_sq_add_cos_sq, mul_one]
    rw [hsc, Real.sqrt_sq hr]
  rw [hint, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Circle boundary crossings**: a coin of radius `r ≥ 0` has expected boundary
    crossings `4r/d`. -/
theorem circle_crossings (r d : ℝ) (hr : 0 ≤ r) (hd : 0 < d) :
    concreteSmoothExpectedCrossings (circle r) 0 (2 * π) d = 4 * r / d := by
  rw [buffon_coin_boundary_crossings (circle r) 0 (2 * π) d hd
        (by positivity) (circle_contDiff r) (circle_closed r),
      circle_perimeter r hr]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hd' : d ≠ 0 := hd.ne'
  field_simp
  ring

/-- **Buffon's coin (classical)**: the expected number of grid lines cutting a
    coin of radius `r ≥ 0` is `2r/d`. For `r ≤ d/2` (diameter `≤ d`) this is the
    crossing probability `diameter / d` — Laplace's 1812 result. -/
theorem circle_lineCuts (r d : ℝ) (hr : 0 ≤ r) (hd : 0 < d) :
    expectedLineCuts (circle r) 0 (2 * π) d = 2 * r / d := by
  unfold expectedLineCuts
  rw [circle_crossings r d hr hd]
  ring

/-! ## Part V: Shape independence -/

/-- **Shape independence**: two convex bodies with equal perimeter have the same
    expected number of cutting lines, regardless of shape. -/
theorem coin_shape_independence
    (γ₁ γ₂ : ℝ → ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hcl₁ : γ₁ a₁ = γ₁ b₁) (hcl₂ : γ₂ a₂ = γ₂ b₂)
    (hP : boundaryPerimeter γ₁ a₁ b₁ = boundaryPerimeter γ₂ a₂ b₂) :
    expectedLineCuts γ₁ a₁ b₁ d = expectedLineCuts γ₂ a₂ b₂ d := by
  rw [buffon_coin_lineCuts γ₁ a₁ b₁ d hd h₁ hC1₁ hcl₁,
      buffon_coin_lineCuts γ₂ a₂ b₂ d hd h₂ hC1₂ hcl₂, hP]

/-- **Monotonicity**: a longer-perimeter convex body has at least as many expected
    cutting lines (same spacing). -/
theorem coin_lineCuts_mono
    (γ₁ γ₂ : ℝ → ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hcl₁ : γ₁ a₁ = γ₁ b₁) (hcl₂ : γ₂ a₂ = γ₂ b₂)
    (hP : boundaryPerimeter γ₁ a₁ b₁ ≤ boundaryPerimeter γ₂ a₂ b₂) :
    expectedLineCuts γ₁ a₁ b₁ d ≤ expectedLineCuts γ₂ a₂ b₂ d := by
  rw [buffon_coin_lineCuts γ₁ a₁ b₁ d hd h₁ hC1₁ hcl₁,
      buffon_coin_lineCuts γ₂ a₂ b₂ d hd h₂ hC1₂ hcl₂]
  apply div_le_div_of_nonneg_right _ (mul_pos Real.pi_pos hd).le
  exact hP

end BuffonsNeedleOQ01OQ04
