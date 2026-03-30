import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

/-
# L'Hôpital's Rule: ∞/∞ Form (OQ-02)

## What This Proves

L'Hôpital's Rule for the ∞/∞ indeterminate form: if f(x) → ∞ and g(x) → ∞
as x → a⁺, and f'(x)/g'(x) → c, then f(x)/g(x) → c.

Mathlib currently provides L'Hôpital's rule only for the 0/0 form (26 variants).
This file adds the ∞/∞ form, which is logically independent: the 0/0 proof
strategy (Cauchy MVT with f(a) = g(a) = 0) does not directly apply when
both functions diverge.

## Proof Strategy

The proof for the ∞/∞ case uses a different argument than the 0/0 case:

1. Reduce to the case c = 0 by defining h(x) = f(x) - c·g(x).
   Then h'(x)/g'(x) = f'(x)/g'(x) - c → 0, and h(x)/g(x) = f(x)/g(x) - c.
   So it suffices to show h(x)/g(x) → 0.

2. For the c = 0 case (f'/g' → 0, g → ∞ ⟹ f/g → 0):
   Fix ε > 0. Choose x₀ near a where |f'(t)/g'(t)| < ε/2 for t near a.
   By Cauchy MVT on [x, x₀] for x < x₀:
     (f(x) - f(x₀))/(g(x) - g(x₀)) = f'(ξ)/g'(ξ)  for some ξ ∈ (x, x₀).
   The algebraic identity gives:
     f(x)/g(x) = [f'(ξ)/g'(ξ)] · [1 - g(x₀)/g(x)] + f(x₀)/g(x)
   As x → a⁺: the first factor has |·| < ε/2, the bracket is in [0,1],
   and f(x₀)/g(x) → 0 since g → ∞. So |f(x)/g(x)| < ε.

## Status
- [x] Statement of ∞/∞ L'Hôpital's rule (right approach)
- [x] Statement of ∞/∞ L'Hôpital's rule (left approach)
- [x] Statement of ∞/∞ L'Hôpital's rule (at +∞)
- [x] Statement of ∞/∞ L'Hôpital's rule (at -∞)
- [x] Proof of right approach via Cauchy MVT
- [ ] Proof of left, at +∞, at -∞ (reductions to right approach)

## Mathlib Dependencies
- `exists_ratio_deriv_eq_ratio_slope` : Cauchy's Mean Value Theorem
- `Filter.Tendsto` : Limit definitions via filters
- `HasDerivAt` : Derivative at a point

## Difficulty: Hard
The ∞/∞ form requires careful epsilon management and the interplay
between two limits (first fix x₀, take x → a⁺, then optimize x₀).
-/

namespace LHopitalInfty

open Set Filter Topology Real

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: THE ∞/∞ L'HÔPITAL'S RULE — RIGHT APPROACH
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **L'Hôpital's Rule — ∞/∞ Form, Right Approach, c = 0**

Special case: if g(x) → +∞ as x → a⁺ and f'(x)/g'(x) → 0, then f(x)/g(x) → 0.

The general case c ≠ 0 reduces to this via the substitution h = f - c·g. -/
private theorem lhopital_infty_right_zero {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hga : Tendsto g (𝓝[>] a) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- Step 1: Get δ₁ where |f'/g'| < ε/2
  rw [Metric.tendsto_nhdsWithin_nhds] at hdiv
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hdiv (ε / 2) hε2
  -- Step 2: Get δ_gpos where g ≥ 1 (so g > 0)
  obtain ⟨δ_gpos, hδ_gpos_pos, hδ_gpos⟩ :
      ∃ δ > (0 : ℝ), ∀ x ∈ Ioi a, dist x a < δ → (1 : ℝ) ≤ g x :=
    Metric.mem_nhdsWithin_iff.mp (Filter.tendsto_atTop.mp hga 1)
  -- Step 3: Choose x₀ ∈ (a, b) with dist x₀ a < δ₁ and g x₀ ≥ 1
  set δ₀ := min (min (δ₁ / 2) ((b - a) / 2)) (δ_gpos / 2)
  have hδ₀_pos : 0 < δ₀ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  set x₀ := a + δ₀
  have hx₀_gt_a : a < x₀ := by linarith
  have hx₀_lt_b : x₀ < b := by
    have h1 : δ₀ ≤ (b - a) / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hx₀_mem : x₀ ∈ Ioo a b := ⟨hx₀_gt_a, hx₀_lt_b⟩
  have hx₀_ioi : x₀ ∈ Ioi a := hx₀_gt_a
  have hx₀_dist_δ₁ : dist x₀ a < δ₁ := by
    rw [Real.dist_eq, abs_of_pos (by linarith : x₀ - a > 0)]
    have h1 : δ₀ ≤ δ₁ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hx₀_dist_gpos : dist x₀ a < δ_gpos := by
    rw [Real.dist_eq, abs_of_pos (by linarith : x₀ - a > 0)]
    have h1 : δ₀ ≤ δ_gpos / 2 := min_le_right _ _
    linarith
  have hgx₀_ge_one : (1 : ℝ) ≤ g x₀ := hδ_gpos x₀ hx₀_ioi hx₀_dist_gpos
  have hgx₀_pos : 0 < g x₀ := by linarith
  -- Step 4: Get δ₂ where g is large enough for correction terms
  -- Need: g(x) > max(g(x₀), 2|f(x₀)|/ε)
  set M := max (g x₀ + 1) (2 * |f x₀| / ε + 1) with hM_def
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :
      ∃ δ > (0 : ℝ), ∀ x ∈ Ioi a, dist x a < δ → M ≤ g x :=
    Metric.mem_nhdsWithin_iff.mp (Filter.tendsto_atTop.mp hga M)
  -- Step 5: Set final δ
  have hx₀a_pos : 0 < x₀ - a := by linarith
  refine ⟨min (x₀ - a) δ₂, lt_min hx₀a_pos hδ₂_pos, fun x hx_ioi hx_dist => ?_⟩
  -- x ∈ Ioi a means a < x; hx_dist : dist x a < min (x₀ - a) δ₂
  -- Extract individual bounds
  have hx_dist_x₀ : dist x a < x₀ - a := lt_of_lt_of_le hx_dist (min_le_left _ _)
  have hx_dist_δ₂ : dist x a < δ₂ := lt_of_lt_of_le hx_dist (min_le_right _ _)
  have hx_pos : 0 < x - a := by linarith [show a < x from hx_ioi]
  -- x < x₀
  have hx_lt_x₀ : x < x₀ := by
    rw [Real.dist_eq, abs_of_pos hx_pos] at hx_dist_x₀; linarith
  -- x ∈ Ioo a b
  have hx_ab : x ∈ Ioo a b := ⟨hx_ioi, lt_trans hx_lt_x₀ hx₀_lt_b⟩
  -- g(x) ≥ M
  have hgx_ge_M : M ≤ g x := hδ₂ x hx_ioi hx_dist_δ₂
  -- g(x) > g(x₀)
  have hgx_gt_gx₀ : g x₀ < g x := by
    have : g x₀ + 1 ≤ M := le_max_left _ _; linarith
  -- g(x) > 0
  have hgx_pos : 0 < g x := lt_trans hgx₀_pos hgx_gt_gx₀
  -- g(x) ≠ 0
  have hgx_ne : g x ≠ 0 := ne_of_gt hgx_pos
  -- g(x) > 2|f(x₀)|/ε
  have hgx_fx₀ : 2 * |f x₀| / ε < g x := by
    have : 2 * |f x₀| / ε + 1 ≤ M := le_max_right _ _; linarith
  -- Step 6: Apply Cauchy MVT on [x, x₀]
  -- First establish [x, x₀] ⊆ (a, b)
  have hIcc_sub : Icc x x₀ ⊆ Ioo a b := fun z ⟨hzx, hzx₀⟩ =>
    ⟨lt_of_lt_of_le hx_ab.1 hzx, lt_of_le_of_lt hzx₀ hx₀_lt_b⟩
  -- ContinuousOn and DifferentiableOn on [x, x₀] and (x, x₀)
  have hf_cont : ContinuousOn f (Icc x x₀) := fun z hz =>
    (hff' z (hIcc_sub hz)).continuousAt.continuousWithinAt
  have hg_cont : ContinuousOn g (Icc x x₀) := fun z hz =>
    (hgg' z (hIcc_sub hz)).continuousAt.continuousWithinAt
  have hf_diff : DifferentiableOn ℝ f (Ioo x x₀) := fun z hz =>
    (hff' z (hIcc_sub (Ioo_subset_Icc_self hz))).differentiableAt.differentiableWithinAt
  have hg_diff : DifferentiableOn ℝ g (Ioo x x₀) := fun z hz =>
    (hgg' z (hIcc_sub (Ioo_subset_Icc_self hz))).differentiableAt.differentiableWithinAt
  -- Apply Cauchy MVT
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_ratio_deriv_eq_ratio_slope f hx_lt_x₀ hf_cont hf_diff g hg_cont hg_diff
  -- hξ_eq : (g x₀ - g x) * deriv f ξ = (f x₀ - f x) * deriv g ξ
  -- ξ ∈ Ioo a b
  have hξ_ab : ξ ∈ Ioo a b := hIcc_sub (Ioo_subset_Icc_self hξ_mem)
  -- deriv f ξ = f' ξ, deriv g ξ = g' ξ
  have hdf : deriv f ξ = f' ξ := (hff' ξ hξ_ab).deriv
  have hdg : deriv g ξ = g' ξ := (hgg' ξ hξ_ab).deriv
  -- g' ξ ≠ 0
  have hg'ξ_ne : g' ξ ≠ 0 := hg' ξ hξ_ab
  -- dist ξ a < δ₁ (ξ < x₀ and dist x₀ a < δ₁)
  have hξ_dist : dist ξ a < δ₁ := by
    rw [Real.dist_eq, abs_of_pos (show 0 < ξ - a by linarith [hξ_ab.1])]
    have : ξ < x₀ := hξ_mem.2
    calc ξ - a < x₀ - a := by linarith
    _ = |x₀ - a| := (abs_of_pos (by linarith)).symm
    _ = dist x₀ a := (Real.dist_eq x₀ a).symm
    _ < δ₁ := hx₀_dist_δ₁
  -- |f'(ξ)/g'(ξ)| < ε/2
  have hξ_bound : dist (f' ξ / g' ξ) 0 < ε / 2 := hδ₁ ξ hξ_ab.1 hξ_dist
  rw [dist_zero_right] at hξ_bound
  -- Step 7: The Cauchy MVT ratio equals f'(ξ)/g'(ξ)
  -- From hξ_eq: (g x₀ - g x) * f' ξ = (f x₀ - f x) * g' ξ
  have hξ_eq' : (g x₀ - g x) * f' ξ = (f x₀ - f x) * g' ξ := by
    rwa [hdf, hdg] at hξ_eq
  -- g x - g x₀ ≠ 0
  have hg_sub_ne : g x - g x₀ ≠ 0 := ne_of_gt (by linarith : 0 < g x - g x₀)
  -- (f x - f x₀) / (g x - g x₀) = f' ξ / g' ξ
  have hR : (f x - f x₀) / (g x - g x₀) = f' ξ / g' ξ := by
    rw [div_eq_div_iff hg_sub_ne hg'ξ_ne]
    -- Goal: (f x - f x₀) * g' ξ = (g x - g x₀) * f' ξ
    -- From hξ_eq': (g x₀ - g x) * f' ξ = (f x₀ - f x) * g' ξ
    -- i.e., -(g x - g x₀) * f' ξ = -(f x - f x₀) * g' ξ
    nlinarith [hξ_eq']
  -- Step 8: Algebraic identity and bound
  -- f(x)/g(x) = [(f(x)-f(x₀))/(g(x)-g(x₀))] · [(g(x)-g(x₀))/g(x)] + f(x₀)/g(x)
  --           = R · (1 - g(x₀)/g(x)) + f(x₀)/g(x)
  -- where R = f'(ξ)/g'(ξ)
  have hident : f x / g x =
      (f' ξ / g' ξ) * (1 - g x₀ / g x) + f x₀ / g x := by
    rw [← hR]; field_simp; ring
  -- Show: dist (f x / g x) 0 < ε, i.e., |f x / g x| < ε
  rw [dist_zero_right, hident]
  -- |R · (1 - g(x₀)/g(x)) + f(x₀)/g(x)| ≤ |R| · |1 - g(x₀)/g(x)| + |f(x₀)/g(x)|
  -- Bound |1 - g(x₀)/g(x)|: since 0 < g(x₀) < g(x), we have 0 < g(x₀)/g(x) < 1
  have hgfrac_pos : 0 < g x₀ / g x := div_pos hgx₀_pos hgx_pos
  have hgfrac_lt_one : g x₀ / g x < 1 := (div_lt_one hgx_pos).mpr hgx_gt_gx₀
  have h1_sub_pos : 0 ≤ 1 - g x₀ / g x := by linarith
  have h1_sub_le_one : 1 - g x₀ / g x ≤ 1 := by linarith [hgfrac_pos]
  -- So |1 - g(x₀)/g(x)| = 1 - g(x₀)/g(x) ∈ [0, 1]
  -- Bound 1: |R · (1 - g(x₀)/g(x))| ≤ |R| · 1 = |R| < ε/2
  -- Bound 2: |f(x₀)/g(x)| = |f(x₀)|/g(x) < ε/2
  calc |f' ξ / g' ξ * (1 - g x₀ / g x) + f x₀ / g x|
      ≤ |f' ξ / g' ξ * (1 - g x₀ / g x)| + |f x₀ / g x| := abs_add _ _
    _ = |f' ξ / g' ξ| * |1 - g x₀ / g x| + |f x₀| / g x := by
        rw [abs_mul, abs_div, abs_of_pos hgx_pos]
    _ ≤ |f' ξ / g' ξ| * 1 + |f x₀| / g x := by
        have := mul_le_mul_of_nonneg_left h1_sub_le_one (abs_nonneg _)
        rw [abs_of_nonneg h1_sub_pos] at this
        linarith
    _ = |f' ξ / g' ξ| + |f x₀| / g x := by ring
    _ < ε / 2 + |f x₀| / g x := by linarith [hξ_bound]
    _ < ε / 2 + ε / 2 := by
        have : |f x₀| / g x < ε / 2 := by
          rw [div_lt_div_iff hgx_pos (by linarith : (0:ℝ) < 2)]
          calc |f x₀| * 2 = 2 * |f x₀| := by ring
            _ < ε * g x := by
                -- g(x) > 2|f(x₀)|/ε, so ε · g(x) > 2|f(x₀)|
                have h1 : 2 * |f x₀| / ε < g x := hgx_fx₀
                have h2 : 0 < ε := hε
                nlinarith
        linarith
    _ = ε := by ring

/-- **L'Hôpital's Rule — ∞/∞ Form, Right Approach**

If f and g are differentiable on (a, b), g(x) → +∞ as x → a⁺,
g'(x) ≠ 0 on (a, b), and f'(x)/g'(x) → c as x → a⁺, then
f(x)/g(x) → c.

Note: We only need g → ∞, not f → ∞. If f also → ∞, the result
follows a fortiori. The crucial hypothesis is g → ∞.

This is complementary to Mathlib's `HasDerivAt.lhopital_zero_right_on_Ioo`
which handles the 0/0 case. -/
theorem lhopital_infty_right {f g f' g' : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hga : Tendsto g (𝓝[>] a) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) (𝓝 c)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 c) := by
  -- Reduce to c = 0 via h(x) = f(x) - c · g(x)
  -- h'(x)/g'(x) = f'(x)/g'(x) - c → 0, and h(x)/g(x) = f(x)/g(x) - c
  -- So f(x)/g(x) → c iff h(x)/g(x) → 0
  set h := fun x => f x - c * g x
  set h' := fun x => f' x - c * g' x
  -- h has derivative h' on (a, b)
  have hh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    (hff' x hx).sub ((hgg' x hx).const_mul c)
  -- h'(x)/g'(x) → 0
  have hdiv_h : Tendsto (fun x => h' x / g' x) (𝓝[>] a) (𝓝 0) := by
    -- h'(x)/g'(x) = f'(x)/g'(x) - c (where g'(x) ≠ 0)
    have heq : (fun x => h' x / g' x) =ᶠ[𝓝[>] a] (fun x => f' x / g' x - c) := by
      filter_upwards [Ioo_mem_nhdsWithin_Ioi (left_mem_Ico.mpr hab)] with x hx
      have hg'_ne : g' x ≠ 0 := hg' x hx
      show (f' x - c * g' x) / g' x = f' x / g' x - c
      field_simp
    rw [Filter.tendsto_congr' heq]
    have := hdiv.sub tendsto_const_nhds
    simp only [sub_self] at this
    exact this
  -- Apply the c = 0 case
  have key : Tendsto (fun x => h x / g x) (𝓝[>] a) (𝓝 0) :=
    lhopital_infty_right_zero hab hh' hgg' hg' hga hdiv_h
  -- f(x)/g(x) = h(x)/g(x) + c (when g(x) ≠ 0)
  have heq_fg : (fun x => f x / g x) =ᶠ[𝓝[>] a] (fun x => h x / g x + c) := by
    filter_upwards [Filter.tendsto_atTop.mp hga 1] with x hx
    have hg_ne : g x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
    show f x / g x = (f x - c * g x) / g x + c
    field_simp
  rw [Filter.tendsto_congr' heq_fg]
  simpa [zero_add] using key.add tendsto_const_nhds

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: ADDITIONAL VARIANTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **∞/∞ L'Hôpital — Left Approach** -/
theorem lhopital_infty_left {f g f' g' : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hgb : Tendsto g (𝓝[<] b) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) (𝓝 c)) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) (𝓝 c) := by
  -- Reduce to right approach via u = a + b - x
  sorry

/-- **∞/∞ L'Hôpital — At +∞** -/
theorem lhopital_infty_atTop {f g f' g' : ℝ → ℝ} {a c : ℝ}
    (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hgTop : Tendsto g atTop atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) atTop (𝓝 c)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 c) := by
  -- Reduce to right approach via u = 1/x
  sorry

/-- **∞/∞ L'Hôpital — At -∞** -/
theorem lhopital_infty_atBot {f g f' g' : ℝ → ℝ} {a c : ℝ}
    (hff' : ∀ x ∈ Iio a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Iio a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Iio a, g' x ≠ 0)
    (hgBot : Tendsto g atBot atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) atBot (𝓝 c)) :
    Tendsto (fun x => f x / g x) atBot (𝓝 c) := by
  -- Reduce to atTop via u = -x
  sorry

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: EXAMPLE APPLICATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-
### Classic Example: lim(x→∞) x/eˣ = 0

Both x and eˣ tend to ∞. By L'Hôpital (∞/∞):
  lim x/eˣ = lim 1/eˣ = 0

This example cannot be handled by the 0/0 form directly.
-/

/-
### Another Example: lim(x→0⁺) ln(x)/cot(x)

Both ln(x) → -∞ and cot(x) → +∞ as x → 0⁺. By L'Hôpital (∞/∞):
  lim ln(x)/cot(x) = lim (1/x)/(-csc²(x)) = lim -sin²(x)/x = 0
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: RELATIONSHIP TO 0/0 FORM
═══════════════════════════════════════════════════════════════════════════════ -/

/-
### Why the ∞/∞ form needs a separate proof

The 0/0 form uses: f(a) = g(a) = 0, so by Cauchy MVT on [a, x]:
  f(x)/g(x) = (f(x) - f(a))/(g(x) - g(a)) = f'(ξ)/g'(ξ)

This fails for ∞/∞ because:
1. f(a) and g(a) don't exist (they're ±∞)
2. The MVT requires the interval to include the point, but x = a is not in the domain

The ∞/∞ proof instead uses a TWO-VARIABLE argument:
1. Fix x₀ near a, apply Cauchy MVT on [x, x₀]
2. Get f(x)/g(x) = [(f(x)-f(x₀))/(g(x)-g(x₀))] · [1-g(x₀)/g(x)] + f(x₀)/g(x)
3. As x → a with x₀ fixed: the correction terms vanish since g → ∞
4. Then optimize by taking x₀ → a as well

The reduction to c = 0 via h(x) = f(x) - c·g(x) simplifies the bookkeeping,
leaving only the case where the derivative ratio tends to 0.
-/

#check lhopital_infty_right
#check lhopital_infty_left
#check lhopital_infty_atTop
#check lhopital_infty_atBot

end LHopitalInfty
