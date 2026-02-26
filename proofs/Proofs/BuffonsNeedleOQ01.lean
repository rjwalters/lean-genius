import Mathlib
import Proofs.BuffonsNeedleOQ01OQ01

/-
# Buffon-Barbier Smooth Curve Theorem: Complete Proof for C¹ Curves (OQ-01)

## What This Proves

This file proves the Buffon-Barbier theorem for C¹ smooth planar curves
requiring ONLY `ContDiff ℝ 1 γ` as the smoothness hypothesis. It fills
the final gap in `BuffonsNeedleOQ01OQ01.lean` by proving that the
`hInnerInt` integrability condition is automatic for C¹ curves.

**Main Result** (`buffon_smooth_of_contDiff`):
For any C¹ curve γ : ℝ → ℝ × ℝ on [a, b] with line spacing d > 0:

  E[crossings] = 2 * arcLength(γ) / (π * d)

## How This Resolves the Open Question

`BuffonsNeedleOQ01OQ01.lean` proved the smooth Buffon-Barbier theorem with an
explicit `hInnerInt` hypothesis. This file proves:

  `ContDiff ℝ 1 γ → IntervalIntegrable (inner integral function) vol a b`

The proof chain:
1. `ContDiff ℝ 1 γ` → `Continuous (fderiv ℝ f)` via `ContDiff.continuous_fderiv`
2. Evaluation at 1 is continuous → `Continuous (deriv f)` for f : ℝ → F
3. `angular_average` → inner integral = `2 * √(dx(t)² + dy(t)²)` for all t
4. Continuity of `2 * √(dx² + dy²)` → `IntervalIntegrable`

## Connection to Prior Work

- `BuffonsNeedle.lean` (Wiedijk #99): straight needle, P = 2ℓ/(πd), 0 sorries
- `BuffonsNoodle.lean`: polygonal noodle, axiom for smooth case
- `BuffonsNeedleOQ01OQ01.lean`: angular average, smooth case with explicit hypotheses
- **This file**: smooth case with ONLY `ContDiff ℝ 1 γ`, 0 sorries, 0 axioms
-/

namespace BuffonsNeedleOQ01

open Real intervalIntegral MeasureTheory
open BuffonsNeedleOQ01OQ01

/-! ## Part I: Derivative Continuity from C¹ Smoothness

The key mathematical fact: for a C¹ curve γ : ℝ → ℝ × ℝ, the component
scalar derivatives are continuous functions of t.

**Proof**: ContDiff ℝ 1 f → Continuous (fderiv ℝ f) via `ContDiff.continuous_fderiv`.
The scalar derivative `deriv f t = fderiv ℝ f t 1`, and evaluation at 1 is continuous.
-/

/-- For f : ℝ → F with `ContDiff ℝ 1 f`, the scalar derivative `deriv f` is continuous.

    The proof uses:
    1. `ContDiff.continuous_fderiv`: f is C¹ → fderiv ℝ f : ℝ → (ℝ →L[ℝ] F) is continuous
    2. `DifferentiableAt.hasFDerivAt.hasDerivAt.deriv`: deriv f t = fderiv ℝ f t 1
    3. Evaluation at 1 is continuous (CLM evaluation is continuous) -/
private lemma contDiff_one_continuous_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ 1 f) : Continuous (deriv f) := by
  -- f is differentiable everywhere (ContDiff ≥ 1 → Differentiable)
  have hdiff : Differentiable ℝ f := hf.differentiable le_rfl
  -- For differentiable f : ℝ → F, deriv f t = fderiv ℝ f t 1 everywhere
  have hderiv_eq : deriv f = fun t => fderiv ℝ f t 1 :=
    funext fun t => hdiff.differentiableAt.hasFDerivAt.hasDerivAt.deriv
  rw [hderiv_eq]
  -- fderiv ℝ f is continuous (from ContDiff ≥ 1); evaluation at 1 is then continuous
  exact (hf.continuous_fderiv le_rfl).clm_apply continuous_const

/-- The x-component derivative `t ↦ deriv (Prod.fst ∘ γ) t` is continuous for a C¹ curve.

    Proof: `Prod.fst ∘ γ` is C¹ (as composition of a smooth projection with γ),
    so `contDiff_one_continuous_deriv` applies. -/
lemma deriv_fst_continuous (γ : ℝ → ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) :
    Continuous (fun t => deriv (Prod.fst ∘ γ) t) :=
  contDiff_one_continuous_deriv (ContDiff.comp contDiff_fst hC1)

/-- The y-component derivative `t ↦ deriv (Prod.snd ∘ γ) t` is continuous for a C¹ curve. -/
lemma deriv_snd_continuous (γ : ℝ → ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) :
    Continuous (fun t => deriv (Prod.snd ∘ γ) t) :=
  contDiff_one_continuous_deriv (ContDiff.comp contDiff_snd hC1)

/-! ## Part II: The Inner Integral is Integrable for C¹ Curves

The angular average identity from BuffonsNeedleOQ01OQ01.lean says:

  ∫_0^π |a sin θ + b cos θ| dθ = 2 √(a² + b²)

So the inner integral in Buffon's formula equals `2 * √(dx(t)² + dy(t)²)`,
which is continuous in t (since dx, dy are continuous). Continuous functions
are interval integrable.
-/

/-- The inner integral equals `2 * √(dx(t)² + dy(t)²)` for each t, by `angular_average`. -/
lemma inner_integral_eq (γ : ℝ → ℝ × ℝ) (t : ℝ) :
    ∫ θ in (0 : ℝ)..π,
      |(deriv (Prod.fst ∘ γ) t) * sin θ + (deriv (Prod.snd ∘ γ) t) * cos θ| =
    2 * Real.sqrt ((deriv (Prod.fst ∘ γ) t) ^ 2 + (deriv (Prod.snd ∘ γ) t) ^ 2) :=
  angular_average _ _

/-- The inner integral function is continuous in t for a C¹ curve.

    **Proof**: Rewrite using `inner_integral_eq` to get `fun t => 2 * √(dx²+dy²)`.
    This is a continuous composition: constant × sqrt(sum of squares of continuous functions). -/
lemma inner_integral_continuous (γ : ℝ → ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) :
    Continuous (fun t =>
      ∫ θ in (0 : ℝ)..π,
        |(deriv (Prod.fst ∘ γ) t) * sin θ + (deriv (Prod.snd ∘ γ) t) * cos θ|) := by
  simp_rw [inner_integral_eq]
  -- Goal: Continuous (fun t => 2 * sqrt(dx(t)^2 + dy(t)^2))
  exact continuous_const.mul
    (Real.continuous_sqrt.comp
      (((deriv_fst_continuous γ hC1).pow 2).add ((deriv_snd_continuous γ hC1).pow 2)))

/-- The inner integral is interval integrable for any C¹ curve on [a, b]. -/
lemma inner_integral_integrable (γ : ℝ → ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) (a b : ℝ) :
    IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π,
        |(deriv (Prod.fst ∘ γ) t) * sin θ + (deriv (Prod.snd ∘ γ) t) * cos θ|)
      volume a b :=
  (inner_integral_continuous γ hC1).intervalIntegrable a b

/-! ## Part III: The Complete Theorem

The main result: for any C¹ curve, the expected number of line crossings
equals 2 * arcLength / (π * d), with NO explicit conditions beyond C¹ smoothness.
-/

/-- **Buffon-Barbier Theorem for C¹ Curves (Complete)**:
    For any C¹ curve γ : ℝ → ℝ × ℝ on [a, b] with d > 0:

      E[crossings] = 2 * arcLength(γ, a, b) / (π * d)

    This depends only on total arc length, not on the shape of γ.

    **All conditions are derived from `ContDiff ℝ 1 γ`** — no explicit
    integrability or measurability conditions needed.

    **Proof**: Apply `buffon_smooth_full` from BuffonsNeedleOQ01OQ01.lean, providing:
    - `hdx`: x-derivative exists everywhere (from ContDiff ≥ 1 → Differentiable)
    - `hdy`: y-derivative exists everywhere (from ContDiff ≥ 1 → Differentiable)
    - `hInnerInt`: inner integral integrable (from `inner_integral_integrable`) -/
theorem buffon_smooth_of_contDiff
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hC1 : ContDiff ℝ 1 γ) :
    concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) :=
  buffon_smooth_full γ a b d hd hab
    -- x-derivative exists (ContDiff 1 → Differentiable → HasDerivAt)
    (fun t _ => (ContDiff.comp contDiff_fst hC1).differentiable le_rfl t |>.hasDerivAt)
    -- y-derivative exists (ContDiff 1 → Differentiable → HasDerivAt)
    (fun t _ => (ContDiff.comp contDiff_snd hC1).differentiable le_rfl t |>.hasDerivAt)
    -- inner integral is integrable (from C¹ smoothness via continuity)
    (inner_integral_integrable γ hC1 a b)

/-! ## Part IV: Shape Independence and Corollaries

Key consequences of the Buffon-Barbier theorem.
-/

/-- **Shape Independence for C¹ Curves**: Two C¹ curves with the same arc length
    have identical expected crossing counts with any parallel line grid.

    The shape of the curve is completely irrelevant — only total arc length matters.
    A circle and a straight line of the same length cross grid lines with the same frequency. -/
theorem smooth_shape_independence
    (γ₁ γ₂ : ℝ → ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hSameLen : planarArcLength γ₁ a₁ b₁ = planarArcLength γ₂ a₂ b₂) :
    concreteSmoothExpectedCrossings γ₁ a₁ b₁ d =
    concreteSmoothExpectedCrossings γ₂ a₂ b₂ d := by
  rw [buffon_smooth_of_contDiff γ₁ a₁ b₁ d hd h₁ hC1₁,
      buffon_smooth_of_contDiff γ₂ a₂ b₂ d hd h₂ hC1₂, hSameLen]

/-- **Straight Line Arc Length**: The horizontal needle γ(t) = (t, 0) on [a, b]
    has arc length b - a. This is the simplest C¹ curve. -/
theorem straight_line_arclength (a b : ℝ) (hab : a ≤ b) :
    planarArcLength (fun t => (t, (0 : ℝ))) a b = b - a := by
  simp only [planarArcLength]
  have hderiv : (fun t : ℝ =>
      Real.sqrt ((deriv (Prod.fst ∘ fun t : ℝ => (t, (0 : ℝ))) t) ^ 2 +
                 (deriv (Prod.snd ∘ fun t : ℝ => (t, (0 : ℝ))) t) ^ 2)) = fun _ => 1 := by
    ext t
    -- Prod.fst ∘ (fun t => (t, 0)) = id, and Prod.snd ∘ (fun t => (t, 0)) = (fun _ => 0)
    have hfst : Prod.fst ∘ (fun t : ℝ => (t, (0 : ℝ))) = id :=
      funext (fun _ => rfl)
    have hsnd : Prod.snd ∘ (fun t : ℝ => (t, (0 : ℝ))) = (fun _ => (0 : ℝ)) :=
      funext (fun _ => rfl)
    have hdx : deriv (Prod.fst ∘ fun t : ℝ => (t, (0 : ℝ))) t = 1 := by
      rw [hfst]; exact (hasDerivAt_id t).deriv
    have hdy : deriv (Prod.snd ∘ fun t : ℝ => (t, (0 : ℝ))) t = 0 := by
      rw [hsnd]; exact (hasDerivAt_const t 0).deriv
    rw [hdx, hdy]; norm_num [Real.sqrt_one]
  rw [hderiv, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- **Straight Line Crossings**: A horizontal needle of length L has expected
    crossings = 2L/(πd) with a parallel line grid of spacing d.

    This confirms that the smooth Buffon-Barbier formula is consistent with
    the original Buffon's Needle result (Wiedijk's 100 Theorems #99). -/
theorem straight_line_crossings (L d : ℝ) (hd : 0 < d) (hL : (0 : ℝ) ≤ L) :
    concreteSmoothExpectedCrossings (fun t => (t, (0 : ℝ))) 0 L d = 2 * L / (π * d) := by
  have hC1 : ContDiff ℝ 1 (fun t : ℝ => (t, (0 : ℝ))) := by fun_prop
  rw [buffon_smooth_of_contDiff _ 0 L d hd hL hC1, straight_line_arclength 0 L hL]
  ring

/-- **Monotonicity**: A longer C¹ curve always has at least as many expected crossings
    as a shorter one (for the same line spacing). -/
theorem smooth_crossings_mono
    (γ₁ γ₂ : ℝ → ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hC1₁ : ContDiff ℝ 1 γ₁) (hC1₂ : ContDiff ℝ 1 γ₂)
    (hlen : planarArcLength γ₁ a₁ b₁ ≤ planarArcLength γ₂ a₂ b₂) :
    concreteSmoothExpectedCrossings γ₁ a₁ b₁ d ≤
    concreteSmoothExpectedCrossings γ₂ a₂ b₂ d := by
  rw [buffon_smooth_of_contDiff γ₁ a₁ b₁ d hd h₁ hC1₁,
      buffon_smooth_of_contDiff γ₂ a₂ b₂ d hd h₂ hC1₂]
  apply div_le_div_of_nonneg_right _ (mul_pos pi_pos hd).le
  linarith

/-- **Limit as d → ∞**: As the line spacing d → ∞, expected crossings → 0.
    This makes physical sense: very widely spaced lines are rarely crossed.
    Proved algebraically: 2L/(πd) → 0 as d → ∞. -/
theorem crossings_tendsto_zero (γ : ℝ → ℝ × ℝ) (a b : ℝ)
    (hab : a ≤ b) (hC1 : ContDiff ℝ 1 γ) :
    Filter.Tendsto
      (fun d => concreteSmoothExpectedCrossings γ a b d)
      Filter.atTop
      (nhds 0) := by
  -- Eventually (for d > 0), concreteSmoothExpectedCrossings = 2L/(πd)
  have heq : ∀ᶠ d in Filter.atTop,
      concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with d hd
    exact buffon_smooth_of_contDiff γ a b d hd hab hC1
  rw [Filter.tendsto_congr' heq]
  -- Prove 2L/(πd) → 0 as d → ∞: 2L/- numerator is constant, denominator πd → ∞
  apply Filter.Tendsto.div_atTop tendsto_const_nhds
  -- Prove πd → ∞ as d → ∞
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  exact ⟨b / π, fun d hd => by
    have hπ := Real.pi_pos
    have hmono := mul_le_mul_of_nonneg_left hd (le_of_lt hπ)
    have hcancel : π * (b / π) = b := by field_simp
    linarith⟩

end BuffonsNeedleOQ01
