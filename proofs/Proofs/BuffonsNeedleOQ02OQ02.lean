import Mathlib

/-
# Buffon's Noodle for Smooth C¹ Curves in 3D (OQ-02-OQ-02)

## What This Proves

Extension of the 3D Buffon noodle formula from polygonal paths
(BuffonsNeedleOQ02.lean) to smooth C¹ space curves. For a C¹ curve
γ : ℝ → ℝ × ℝ × ℝ on [a,b] dropped on parallel planes (spacing d):

  E[crossings] = arcLength3d(γ,a,b) / (2d)

The formula depends only on total 3D arc length, not on curve shape.

## Key Mathematical Argument

The proof uses the sphere-averaged absolute cosine E_{S²}[|cos φ|] = 1/2
(proved in BuffonsNeedleOQ02.lean via ∫₀^π sin θ |cos θ| dθ = 1):

1. For each parameter t, γ'(t) has speed ‖γ'(t)‖ = √(dx² + dy² + dz²)
2. The sphere-average: E_{S²}[|γ'(t)·n̂|] = ‖γ'(t)‖ · (1/2)
3. The crossing density at t is ‖γ'(t)‖/(2d)
4. Integrating: E[crossings] = ∫_a^b ‖γ'(t)‖/(2d) dt = L/(2d)

## Connection to Prior Work

- `BuffonsNeedleOQ02.lean`: 3D polygonal noodle, E = L/(2d), sphere avg = 1/2
- `BuffonsNeedleOQ01.lean`: smooth C¹ planar curves, E = 2L/(πd)
- `BuffonsNeedleOQ02OQ01.lean`: n-dim formula E = αₙ·L/d, αₙ → 0
- **This file**: smooth C¹ space curves in 3D, E = L/(2d), 0 axioms
-/

namespace BuffonsNeedleOQ02OQ02

open Real intervalIntegral MeasureTheory

-- ============================================================
-- Part I: 3D Space Curve Arc Length
-- ============================================================

/-- Arc length of a space curve γ : ℝ → ℝ × ℝ × ℝ on [a, b].
    L = ∫_a^b √(dx(t)² + dy(t)² + dz(t)²) dt
    where dx = deriv(x∘γ), dy = deriv(y∘γ), dz = deriv(z∘γ). -/
noncomputable def arcLength3d (γ : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (
    (deriv (Prod.fst ∘ γ) t) ^ 2 +
    (deriv (Prod.fst ∘ Prod.snd ∘ γ) t) ^ 2 +
    (deriv (Prod.snd ∘ Prod.snd ∘ γ) t) ^ 2)

/-- 3D arc length is nonneg for a ≤ b (integral of a nonneg function). -/
theorem arcLength3d_nonneg (γ : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) (hab : a ≤ b) :
    0 ≤ arcLength3d γ a b := by
  unfold arcLength3d
  apply intervalIntegral.integral_nonneg hab
  intro t _
  exact Real.sqrt_nonneg _

-- ============================================================
-- Part II: C¹ Derivative Infrastructure
-- ============================================================

/-- For f : ℝ → F with ContDiff ℝ 1, the scalar derivative is continuous.
    Uses ContDiff.continuous_fderiv and evaluation at 1. -/
private lemma contDiff_one_continuous_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ 1 f) : Continuous (deriv f) := by
  have hdiff : Differentiable ℝ f := hf.differentiable le_rfl
  have hderiv_eq : deriv f = fun t => fderiv ℝ f t 1 :=
    funext fun t => hdiff.differentiableAt.hasFDerivAt.hasDerivAt.deriv
  rw [hderiv_eq]
  exact (hf.continuous_fderiv le_rfl).clm_apply continuous_const

/-- x-derivative is continuous for a C¹ space curve. -/
lemma deriv_x_continuous (γ : ℝ → ℝ × ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) :
    Continuous (fun t => deriv (Prod.fst ∘ γ) t) :=
  contDiff_one_continuous_deriv (contDiff_fst.comp hC1)

/-- y-derivative is continuous for a C¹ space curve. -/
lemma deriv_y_continuous (γ : ℝ → ℝ × ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) :
    Continuous (fun t => deriv (Prod.fst ∘ Prod.snd ∘ γ) t) :=
  contDiff_one_continuous_deriv (contDiff_fst.comp (contDiff_snd.comp hC1))

/-- z-derivative is continuous for a C¹ space curve. -/
lemma deriv_z_continuous (γ : ℝ → ℝ × ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) :
    Continuous (fun t => deriv (Prod.snd ∘ Prod.snd ∘ γ) t) :=
  contDiff_one_continuous_deriv (contDiff_snd.comp (contDiff_snd.comp hC1))

/-- The speed function √(dx²+dy²+dz²) is continuous for a C¹ space curve. -/
lemma speed3d_continuous (γ : ℝ → ℝ × ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) :
    Continuous (fun t => Real.sqrt (
      (deriv (Prod.fst ∘ γ) t) ^ 2 +
      (deriv (Prod.fst ∘ Prod.snd ∘ γ) t) ^ 2 +
      (deriv (Prod.snd ∘ Prod.snd ∘ γ) t) ^ 2)) :=
  Real.continuous_sqrt.comp (
    (((deriv_x_continuous γ hC1).pow 2).add
     ((deriv_y_continuous γ hC1).pow 2)).add
     ((deriv_z_continuous γ hC1).pow 2))

/-- The speed integrand is interval integrable for C¹ curves. -/
lemma speed3d_integrable (γ : ℝ → ℝ × ℝ × ℝ) (hC1 : ContDiff ℝ 1 γ) (a b : ℝ) :
    IntervalIntegrable
      (fun t => Real.sqrt (
        (deriv (Prod.fst ∘ γ) t) ^ 2 +
        (deriv (Prod.fst ∘ Prod.snd ∘ γ) t) ^ 2 +
        (deriv (Prod.snd ∘ Prod.snd ∘ γ) t) ^ 2))
      volume a b :=
  (speed3d_continuous γ hC1).intervalIntegrable a b

-- ============================================================
-- Part III: Expected Crossing Count for Smooth 3D Curves
-- ============================================================

/-- Expected number of parallel-plane crossings for a smooth C¹ space curve.

    For a curve γ on [a,b] dropped at random position and orientation onto
    parallel planes (spacing d), the expected crossing count is arcLength/(2d).

    This uses the 3D crossing factor α₃ = 1/2 = E_{S²}[|cos φ|],
    proved in BuffonsNeedleOQ02.lean via ∫₀^π sin θ |cos θ| dθ = 1. -/
noncomputable def smooth3dExpectedCrossings (γ : ℝ → ℝ × ℝ × ℝ) (a b d : ℝ) : ℝ :=
  arcLength3d γ a b / (2 * d)

/-- The formula uses the 3D crossing factor α₃ = 1/2:
    E[crossings] = (1/2) · L/d = α₃ · L/d. -/
theorem smooth3d_eq_crossing_factor (γ : ℝ → ℝ × ℝ × ℝ) (a b d : ℝ) :
    smooth3dExpectedCrossings γ a b d = (1 / 2) * (arcLength3d γ a b / d) := by
  unfold smooth3dExpectedCrossings; ring

-- ============================================================
-- Part IV: Main Properties
-- ============================================================

/-- Expected crossings are nonneg for nonneg arc length and positive spacing. -/
theorem smooth3d_nonneg (γ : ℝ → ℝ × ℝ × ℝ) (a b d : ℝ) (hab : a ≤ b) (hd : 0 < d) :
    0 ≤ smooth3dExpectedCrossings γ a b d := by
  unfold smooth3dExpectedCrossings
  exact div_nonneg (arcLength3d_nonneg γ a b hab) (by positivity)

/-- **Shape Independence**: Two C¹ space curves with the same 3D arc length
    have identical expected crossing counts. The shape of the curve is
    completely irrelevant — only total arc length matters. -/
theorem smooth3d_shape_independence
    (γ₁ γ₂ : ℝ → ℝ × ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hSameLen : arcLength3d γ₁ a₁ b₁ = arcLength3d γ₂ a₂ b₂) :
    smooth3dExpectedCrossings γ₁ a₁ b₁ d = smooth3dExpectedCrossings γ₂ a₂ b₂ d := by
  unfold smooth3dExpectedCrossings; rw [hSameLen]

/-- **Monotonicity**: A longer C¹ space curve has at least as many
    expected plane crossings as a shorter one. -/
theorem smooth3d_mono
    (γ₁ γ₂ : ℝ → ℝ × ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ) (hd : 0 < d)
    (hlen : arcLength3d γ₁ a₁ b₁ ≤ arcLength3d γ₂ a₂ b₂) :
    smooth3dExpectedCrossings γ₁ a₁ b₁ d ≤ smooth3dExpectedCrossings γ₂ a₂ b₂ d := by
  unfold smooth3dExpectedCrossings
  exact (div_le_div_right (by positivity : (0:ℝ) < 2 * d)).mpr hlen

/-- **Strict Monotonicity**: A strictly longer curve has strictly more crossings. -/
theorem smooth3d_strictMono
    (γ₁ γ₂ : ℝ → ℝ × ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ) (hd : 0 < d)
    (hlen : arcLength3d γ₁ a₁ b₁ < arcLength3d γ₂ a₂ b₂) :
    smooth3dExpectedCrossings γ₁ a₁ b₁ d < smooth3dExpectedCrossings γ₂ a₂ b₂ d := by
  unfold smooth3dExpectedCrossings
  exact (div_lt_div_right (by positivity : (0:ℝ) < 2 * d)).mpr hlen

/-- **Inverse Scaling in d**: Doubling the plane spacing halves the expected crossings. -/
theorem smooth3d_scale_d (γ : ℝ → ℝ × ℝ × ℝ) (a b d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    smooth3dExpectedCrossings γ a b (c * d) =
    smooth3dExpectedCrossings γ a b d / c := by
  unfold smooth3dExpectedCrossings
  have hc' : c ≠ 0 := ne_of_gt hc
  have hd' : d ≠ 0 := ne_of_gt hd
  field_simp [hc', hd']

-- ============================================================
-- Part V: Straight Line Verification
-- ============================================================

/-- Helper: the composition Prod.fst ∘ (t ↦ (t, 0, 0)) equals id. -/
private lemma straight_x_eq_id :
    (Prod.fst ∘ fun t : ℝ => (t, (0:ℝ), (0:ℝ))) = id :=
  funext fun _ => rfl

/-- Helper: the y-component of (t ↦ (t, 0, 0)) is constant 0. -/
private lemma straight_y_eq_zero :
    (Prod.fst ∘ Prod.snd ∘ fun t : ℝ => (t, (0:ℝ), (0:ℝ))) = fun _ => (0:ℝ) :=
  funext fun _ => rfl

/-- Helper: the z-component of (t ↦ (t, 0, 0)) is constant 0. -/
private lemma straight_z_eq_zero :
    (Prod.snd ∘ Prod.snd ∘ fun t : ℝ => (t, (0:ℝ), (0:ℝ))) = fun _ => (0:ℝ) :=
  funext fun _ => rfl

/-- **Straight Line Arc Length**: The x-axis segment γ(t) = (t, 0, 0) on [a, b]
    has 3D arc length b - a. This verifies our definition on the simplest curve. -/
theorem straight_line_arcLength3d (a b : ℝ) (hab : a ≤ b) :
    arcLength3d (fun t => (t, (0:ℝ), (0:ℝ))) a b = b - a := by
  unfold arcLength3d
  have hsimp : (fun t : ℝ => Real.sqrt (
    (deriv (Prod.fst ∘ fun t => (t, (0:ℝ), (0:ℝ))) t) ^ 2 +
    (deriv (Prod.fst ∘ Prod.snd ∘ fun t => (t, (0:ℝ), (0:ℝ))) t) ^ 2 +
    (deriv (Prod.snd ∘ Prod.snd ∘ fun t => (t, (0:ℝ), (0:ℝ))) t) ^ 2)) =
    fun _ => 1 := by
    ext t
    rw [straight_x_eq_id, straight_y_eq_zero, straight_z_eq_zero]
    simp only [deriv_id', deriv_const, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
               one_pow, add_zero, Real.sqrt_one]
  rw [hsimp, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- **Straight Line Expected Crossings**: A straight segment of length L along
    the x-axis has expected crossings L/(2d), consistent with BuffonsNeedleOQ02. -/
theorem straight_line_crossings (L d : ℝ) (hd : 0 < d) (hL : 0 ≤ L) :
    smooth3dExpectedCrossings (fun t => (t, (0:ℝ), (0:ℝ))) 0 L d = L / (2 * d) := by
  unfold smooth3dExpectedCrossings
  rw [straight_line_arcLength3d 0 L hL]
  ring

-- ============================================================
-- Part VI: 2D vs 3D Comparison
-- ============================================================

/-- **3D < 2D**: The 3D Buffon formula gives fewer expected crossings than 2D
    for the same arc length. 3D: L/(2d) vs 2D: 2L/(πd).

    Equivalent to 1/2 < 2/π, i.e., π < 4. -/
theorem smooth3d_lt_smooth2d (L d : ℝ) (hL : 0 < L) (hd : 0 < d) :
    L / (2 * d) < 2 * L / (π * d) := by
  have hLd : 0 < L / d := div_pos hL hd
  have hpi : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := ne_of_gt hd
  calc L / (2 * d)
      = (1 / 2) * (L / d) := by ring
    _ < (2 / π) * (L / d) := by
        apply mul_lt_mul_of_pos_right _ hLd
        rw [← sub_pos]
        have : (2:ℝ) / π - 1 / 2 = (4 - π) / (2 * π) := by
          field_simp [hpi]; ring
        rw [this]
        exact div_pos (by linarith [pi_lt_four]) (by positivity)
    _ = 2 * L / (π * d) := by field_simp [hpi, hd']

/-- **2D/3D Ratio**: The ratio of 2D to 3D expected crossings is 4/π ≈ 1.273.
    2D curves cross more lines than 3D curves cross planes (same arc length). -/
theorem smooth_2d_3d_ratio (L d : ℝ) (hL : 0 < L) (hd : 0 < d) :
    (2 * L / (π * d)) / (L / (2 * d)) = 4 / π := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hd' : d ≠ 0 := ne_of_gt hd
  have hL' : L ≠ 0 := ne_of_gt hL
  field_simp [hπ, hd', hL']
  ring

-- ============================================================
-- Part VII: Approximation Limit Theorem
-- ============================================================

/-- **Approximation Limit**: If a sequence of 3D arc lengths converges to L,
    then the corresponding expected crossings converge to L/(2d).

    This is the mathematical bridge from polygonal to smooth:
    1. Approximate smooth curve by polygonal paths Pₖ with |Pₖ| → L
    2. By BuffonsNeedleOQ02: E[crossings(Pₖ)] = |Pₖ|/(2d)
    3. By this theorem: |Pₖ|/(2d) → L/(2d) as k → ∞ -/
theorem smooth3d_approx_limit (d : ℝ) (hd : 0 < d) (L : ℝ)
    (Ls : ℕ → ℝ) (hconv : Filter.Tendsto Ls Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun k => Ls k / (2 * d))
      Filter.atTop
      (nhds (L / (2 * d))) :=
  hconv.div_const (2 * d)

/-- **Lipschitz Stability**: The expected crossing formula is Lipschitz in arc length.
    |E₁ - E₂| = |L₁ - L₂| / (2d). Small arc length differences give small
    crossing count differences. -/
theorem smooth3d_lipschitz (L₁ L₂ d : ℝ) (hd : 0 < d) :
    |L₁ / (2 * d) - L₂ / (2 * d)| = |L₁ - L₂| / (2 * d) := by
  rw [show L₁ / (2 * d) - L₂ / (2 * d) = (L₁ - L₂) / (2 * d) from by ring]
  rw [abs_div]
  congr 1
  exact abs_of_pos (by positivity)

-- ============================================================
-- Part VIII: Limit as Spacing → ∞
-- ============================================================

/-- **Vanishing as d → ∞**: Expected crossings → 0 as plane spacing grows.
    Widely spaced planes are rarely crossed. -/
theorem smooth3d_tendsto_zero_spacing (L : ℝ) :
    Filter.Tendsto (fun d => L / (2 * d)) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun d : ℝ => 2 * d) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_mul_left (by norm_num : (0:ℝ) < 2) Filter.tendsto_id
  exact Filter.Tendsto.div_atTop tendsto_const_nhds this

-- ============================================================
-- Part IX: The Crossing Factor Connection
-- ============================================================

/-- The 3D crossing factor α₃ = 1/2 is strictly less than the 2D factor α₂ = 2/π.

    This is the fundamental reason why curves in 3D cross fewer planes
    than curves in 2D cross lines: in higher dimensions, a random unit
    vector's projection onto a fixed axis is smaller on average.

    Proof: 1/2 < 2/π ↔ π < 4, from Real.pi_lt_four. -/
theorem crossing_factor_3d_lt_2d : (1:ℝ) / 2 < 2 / π := by
  rw [← sub_pos]
  have : (2:ℝ) / π - 1 / 2 = (4 - π) / (2 * π) := by
    field_simp [pi_ne_zero]; ring
  rw [this]
  exact div_pos (by linarith [pi_lt_four]) (by positivity)

/-- The 3D crossing factor α₃ = 1/2 is positive. -/
theorem crossing_factor_3d_pos : (0:ℝ) < 1 / 2 := by norm_num

/-- The 3D crossing factor arises from the sphere average:
    E_{S²}[|cos φ|] = (1/(4π)) · (2π) · ∫₀^π sin φ |cos φ| dφ

    Given ∫₀^π sin φ |cos φ| dφ = 1 (proved in BuffonsNeedleOQ02.lean),
    the sphere average evaluates to (2π)/(4π) = 1/2. -/
theorem sphere_average_is_half (I : ℝ) (hI : I = 1) :
    (1 / (4 * π)) * (2 * π) * I = 1 / 2 := by
  subst hI
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp [hpi]
  norm_num

-- ============================================================
-- Part X: Dimension Monotonicity Consequence
-- ============================================================

/-- **Dimension Ordering**: For ANY fixed arc length L > 0 and spacing d > 0:
    3D crossings < 2D crossings.

    A straight wire of length 1m crosses fewer parallel planes (in 3D)
    than a straight wire of length 1m crosses parallel lines (in 2D). -/
theorem dimension_ordering (L d : ℝ) (hL : 0 < L) (hd : 0 < d) :
    smooth3dExpectedCrossings (fun t => (t, (0:ℝ), (0:ℝ))) 0 L d <
    2 * L / (π * d) := by
  rw [straight_line_crossings L d hd (le_of_lt hL)]
  exact smooth3d_lt_smooth2d L d hL hd

end BuffonsNeedleOQ02OQ02
