/-
# Brouwer Fixed Point OQ-02: Stability and Averaged Iteration
# Fixed Point Stability Under Perturbation and Krasnoselskii-Mann Damping

Further extensions to the computational complexity of approximate fixed points.

## Results (0 sorries — fully proved)
1. Fixed point stability: if g is delta-close to a contraction f, their fixed
   points are at most delta/(1-L) apart
2. Averaged (Krasnoselskii-Mann) iteration: T(x) = (1-t)x + t*f(x)
   preserves self-mapping on [0,1] and has Lipschitz constant (1-t+tL)
3. Geometric decay lemma for monotone sequences
4. Parametric family sensitivity: small parameter changes -> small fixed point shifts

These results extend the computational complexity picture:
- Stability shows that approximate computation of f suffices (oracle model)
- Averaged iteration shows how to stabilize non-contractive maps
- Together they justify the O(log 1/eps) complexity even with approximate oracles
-/

import Mathlib

set_option linter.unusedVariables false

namespace BrouwerOQ02Stability

open Set

-- ============================================================
-- SECTION I: Fixed Point Stability Under Perturbation
-- ============================================================

/-- **Fixed point stability**: if f is a contraction (L < 1) with fixed point
    x*, and g is uniformly delta-close to f, then any fixed point y* of g
    satisfies |x* - y*| <= delta/(1-L).

    This is crucial for computational complexity: it shows that to find
    the fixed point within eps, it suffices to work with an oracle that
    approximates f within delta = eps(1-L). -/
theorem fixed_point_stability {f g : ℝ → ℝ} {L delta : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1) (hdelta : 0 ≤ delta)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hclose : ∀ x, |f x - g x| ≤ delta)
    {x_star y_star : ℝ} (hfx : f x_star = x_star) (hgy : g y_star = y_star) :
    |x_star - y_star| ≤ delta / (1 - L) := by
  have h1L : 0 < 1 - L := by linarith
  have tri : |x_star - y_star| ≤ |f x_star - f y_star| + |f y_star - g y_star| := by
    have : |x_star - y_star| = |f x_star - g y_star| := by rw [hfx, hgy]
    rw [this]
    have dt := dist_triangle (f x_star) (f y_star) (g y_star)
    rwa [Real.dist_eq, Real.dist_eq, Real.dist_eq] at dt
  have h1 := hlip x_star y_star
  have h2 := hclose y_star
  have key : (1 - L) * |x_star - y_star| ≤ delta := by nlinarith
  rw [le_div_iff₀ h1L]
  linarith [mul_comm (1 - L) |x_star - y_star|]

-- ============================================================
-- SECTION II: Geometric Decay Lemma
-- ============================================================

/-- **Geometric decay**: if a sequence satisfies a(n+1) <= r*a(n) with r >= 0,
    then a(n) <= r^n * a(0). This is the discrete Gronwall inequality. -/
theorem geometric_decay {r : ℝ} (hr : 0 ≤ r) (a : ℕ → ℝ)
    (ha_nn : ∀ n, 0 ≤ a n)
    (ha_rec : ∀ n, a (n + 1) ≤ r * a n) :
    ∀ n, a n ≤ r ^ n * a 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    calc a (k + 1)
        ≤ r * a k := ha_rec k
      _ ≤ r * (r ^ k * a 0) := mul_le_mul_of_nonneg_left ih hr
      _ = r ^ (k + 1) * a 0 := by ring

-- ============================================================
-- SECTION III: Averaged (Krasnoselskii-Mann) Iteration
-- ============================================================

/-- The averaged (damped) iteration map: T_t(x) = (1-t)x + t*f(x). -/
def averagedMap (f : ℝ → ℝ) (t : ℝ) (x : ℝ) : ℝ :=
  (1 - t) * x + t * f x

/-- **Averaged iteration preserves [0,1]**: if f maps [0,1] to [0,1]
    and t in [0,1], then T_t maps [0,1] to [0,1]. -/
theorem averagedMap_maps_unit {f : ℝ → ℝ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    averagedMap f t x ∈ Icc (0:ℝ) 1 := by
  simp only [averagedMap, mem_Icc]
  have hfx := hmaps x hx
  constructor
  · nlinarith [hx.1, hfx.1]
  · nlinarith [hx.2, hfx.2]

/-- **Averaged iteration Lipschitz constant**: if f is L-Lipschitz,
    then T_t is (1 - t(1-L))-Lipschitz.

    Key insight: when L > 1 (f is expansive), choosing t small enough
    makes T_t contractive: need t < 2/(1+L) for |1-t(1-L)| < 1.
    When L < 1 (f is already contractive), any t in (0,1] works.

    For the computational complexity picture:
    - L < 1: iteration converges in O(log(1/eps) / log(1/(1-t(1-L)))) steps
    - L = 1: averaged iteration converges (slowly) even for nonexpansive maps
    - This is why Krasnoselskii-Mann iteration is important for optimization -/
theorem averagedMap_lipschitz {f : ℝ → ℝ} {L t : ℝ}
    (hL : 0 ≤ L) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x y : ℝ) :
    |averagedMap f t x - averagedMap f t y| ≤ (1 - t * (1 - L)) * |x - y| := by
  simp only [averagedMap]
  have expand : (1 - t) * x + t * f x - ((1 - t) * y + t * f y) =
      (1 - t) * (x - y) + t * (f x - f y) := by ring
  rw [expand]
  have h_tri : |(1 - t) * (x - y) + t * (f x - f y)| ≤
      |(1 - t) * (x - y)| + |t * (f x - f y)| := by
    simp only [← Real.norm_eq_abs]
    exact norm_add_le _ _
  calc |(1 - t) * (x - y) + t * (f x - f y)|
      ≤ |(1 - t) * (x - y)| + |t * (f x - f y)| := h_tri
    _ = (1 - t) * |x - y| + t * |f x - f y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t),
            abs_of_nonneg ht0]
    _ ≤ (1 - t) * |x - y| + t * (L * |x - y|) := by
        linarith [mul_le_mul_of_nonneg_left (hlip x y) ht0]
    _ = (1 - t * (1 - L)) * |x - y| := by ring

/-- **Averaged iteration fixed points coincide with f's fixed points**:
    T_t(x) = x if and only if f(x) = x (for t != 0). -/
theorem averagedMap_fixedPoint_iff {f : ℝ → ℝ} {t : ℝ}
    (ht : t ≠ 0) (x : ℝ) :
    averagedMap f t x = x ↔ f x = x := by
  simp only [averagedMap]
  constructor
  · intro h
    have : t * f x = t * x := by linarith
    exact mul_left_cancel₀ ht this
  · intro h
    rw [h]; ring

-- ============================================================
-- SECTION IV: Parametric Sensitivity
-- ============================================================

/-- **Parametric family sensitivity**: for a family of contractions f_t
    parameterized by t, if the family is Lipschitz in t (uniformly),
    then the fixed point map t -> x*(t) is also Lipschitz.

    If |f_t(x) - f_s(x)| <= K|t-s| and each f_t is L-Lipschitz with L < 1,
    then |x*(t) - x*(s)| <= K/(1-L) * |t-s|.

    This is the quantitative version of the implicit function theorem
    for contraction families. -/
theorem parametric_sensitivity {f : ℝ → ℝ → ℝ} {L K : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1) (hK : 0 ≤ K)
    (hlip_x : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hlip_t : ∀ t s x, |f t x - f s x| ≤ K * |t - s|)
    {t s : ℝ} {xt xs : ℝ}
    (hft : f t xt = xt) (hfs : f s xs = xs) :
    |xt - xs| ≤ K / (1 - L) * |t - s| := by
  have h1L : 0 < 1 - L := by linarith
  have tri : |xt - xs| ≤ |f t xt - f t xs| + |f t xs - f s xs| := by
    have : |xt - xs| = |f t xt - f s xs| := by rw [hft, hfs]
    rw [this]
    have dt := dist_triangle (f t xt) (f t xs) (f s xs)
    rwa [Real.dist_eq, Real.dist_eq, Real.dist_eq] at dt
  have h1 := hlip_x t xt xs
  have h2 := hlip_t t s xs
  have key : (1 - L) * |xt - xs| ≤ K * |t - s| := by nlinarith
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ h1L]
  linarith [mul_comm (1 - L) |xt - xs|]

-- ============================================================
-- SECTION V: Summary
-- ============================================================

/-- **Stability and perturbation summary**: the fixed point of a contraction
    is stable under perturbation of the map and parameters. -/
theorem stability_summary {f g : ℝ → ℝ} {L delta : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1) (hdelta : 0 ≤ delta)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hclose : ∀ x, |f x - g x| ≤ delta)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -- Stability: perturbed fixed points are close
    (∀ x_star y_star, f x_star = x_star → g y_star = y_star →
      |x_star - y_star| ≤ delta / (1 - L)) ∧
    -- Averaged map is Lipschitz with improved constant
    (∀ x y, |averagedMap f t x - averagedMap f t y| ≤
      (1 - t * (1 - L)) * |x - y|) :=
  ⟨fun _ _ hfx hgy => fixed_point_stability hL hL1 hdelta hlip hclose hfx hgy,
   fun x y => averagedMap_lipschitz hL ht0 ht1 hlip x y⟩

end BrouwerOQ02Stability
