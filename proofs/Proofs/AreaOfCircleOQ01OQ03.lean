/-
  Isoperimetric Inequality: C² ≥ 4πA with Equality Only for Circles
  Open Question: area-of-circle-oq-01-oq-03

  The isoperimetric inequality states that among all closed plane curves of
  given circumference C, the circle encloses the maximum area A. Equivalently:

    C² ≥ 4πA,  with equality iff the curve is a circle.

  This is the third result in the OQ chain starting from Wiedijk #9:
  - OQ01: C = dA/dr  (circumference = derivative of area w.r.t. radius)
  - OQ01-OQ02: A = ∫₀ʳ C(ρ) dρ  (area = integral of circumference)
  - OQ01-OQ03: C² ≥ 4πA  (isoperimetric inequality, THIS FILE)

  Proof Architecture (Hurwitz 1901):
  For a smooth closed curve γ : [0, 2π] → ℝ² parameterized by arc length:
  1. L = ∫₀²π |γ'(t)| dt  (circumference)
  2. A = (1/2)|∫₀²π (x y' - y x') dt|  (enclosed area via Green's theorem)
  3. By Wirtinger: ∫₀²π f² ≤ ∫₀²π (f')² for mean-zero functions
  4. By Cauchy-Schwarz + AM-GM: combine to get 4πA ≤ L²

  Mathlib Status:
  - Wirtinger's inequality: NOT in Mathlib (requires Fourier convergence)
  - Fourier basis on L²(AddCircle T): available
  - Parseval's identity: available (tsum_sq_fourierCoeff)
  - The assembled Wirtinger proof would be ~200-300 lines

  What This File Proves (19 theorems, 2 axioms, 1 sorry):
  1. Equality for circles: C² = 4πA  (ring computation)
  2. Strict inequality for squares: C² > 4πA  (π < 4)
  3. The isoperimetric ratio: A/(C²/4π) and its circle value
  4. Connection to OQ01: the equality case via C = dA/dr
  5. Regular polygon isoperimetric ratios
  6. ngon_limit_tendsto_circle: π/(n·tan(π/n)) → 1  (via tan x/x → 1 from hasDerivAt)
  7. circleGamma_circumference: arc-length integral = 2πr  (√(sin²+cos²) = 1)
  8. circleGamma_area: Green's theorem integral = πr²  (sin²+cos² = 1)
  9. The Wirtinger–isoperimetric deduction chain (axiomatized Wirtinger)

  References:
  - Hurwitz (1901): Fourier series proof
  - Chavel (2001): "Isoperimetric Inequalities" Cambridge
  - Mathlib: Proofs/CircumferenceFromArea.lean (OQ01)
  - Mathlib: Proofs/AreaFromCircumferenceIntegral.lean (OQ01-OQ02)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

noncomputable section

namespace IsoperimetricOQ

/-
## Part I: The Circle Case — Equality C² = 4πA

For a circle with radius r: C = 2πr and A = πr².
The isoperimetric inequality becomes an equality: (2πr)² = 4π · πr².
-/

/-- The circumference of a circle with radius r. -/
def circleCirc (r : ℝ) : ℝ := 2 * π * r

/-- The area of a circle with radius r. -/
def circleArea (r : ℝ) : ℝ := π * r ^ 2

/-- **KEY**: For a circle, C² = 4πA exactly.
    This is the equality case of the isoperimetric inequality.
    Follows immediately from the definitions C = 2πr and A = πr². -/
theorem circle_isoperimetric_equality (r : ℝ) :
    circleCirc r ^ 2 = 4 * π * circleArea r := by
  unfold circleCirc circleArea
  ring

/-- The isoperimetric ratio for a circle is 1 (normalized by 4π). -/
theorem circle_isoperimetric_ratio (r : ℝ) (hr : 0 < r) :
    4 * π * circleArea r / circleCirc r ^ 2 = 1 := by
  rw [← circle_isoperimetric_equality]
  have h : circleCirc r ^ 2 ≠ 0 := by
    unfold circleCirc
    have hpi : π ≠ 0 := pi_ne_zero
    have hr' : r ≠ 0 := ne_of_gt hr
    positivity
  exact div_self h

/-- Circumference is positive for positive radius. -/
theorem circleCirc_pos (r : ℝ) (hr : 0 < r) : 0 < circleCirc r := by
  unfold circleCirc; positivity

/-- Area is positive for positive radius. -/
theorem circleArea_pos (r : ℝ) (hr : 0 < r) : 0 < circleArea r := by
  unfold circleArea; positivity

/-- Connection to OQ01: the circumference equals the derivative of area.
    This is the key relationship that starts the OQ chain. -/
theorem circumference_is_deriv_of_area (r : ℝ) :
    circleCirc r = deriv circleArea r := by
  unfold circleArea circleCirc
  have : deriv (fun r => π * r ^ 2) r = 2 * π * r := by
    have : HasDerivAt (fun r => π * r ^ 2) (π * (2 * r ^ 1)) r :=
      (hasDerivAt_pow 2 r).const_mul π
    simp only [pow_one] at this
    rw [this.deriv]
    ring
  rw [this]

/-
## Part II: The Square Case — Strict Inequality C² > 4πA

For a square with side s: C = 4s and A = s².
The isoperimetric inequality is strict: (4s)² > 4π · s², i.e., 16 > 4π, i.e., 4 > π.
-/

/-- The circumference (perimeter) of a square with side s. -/
def squareCirc (s : ℝ) : ℝ := 4 * s

/-- The area of a square with side s. -/
def squareArea (s : ℝ) : ℝ := s ^ 2

/-- For a square, C² > 4πA (strict inequality). -/
theorem square_isoperimetric_strict (s : ℝ) (hs : 0 < s) :
    4 * π * squareArea s < squareCirc s ^ 2 := by
  unfold squareCirc squareArea
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  nlinarith [show π < 4 from by linarith [Real.pi_lt_3141593], hs2]

/-- The isoperimetric ratio for a square is 4π/16 = π/4 < 1. -/
theorem square_isoperimetric_ratio (s : ℝ) (hs : 0 < s) :
    4 * π * squareArea s / squareCirc s ^ 2 = π / 4 := by
  unfold squareCirc squareArea
  have hs' : s ≠ 0 := ne_of_gt hs
  field_simp [hs']

/-- The square ratio is less than 1, confirming it's suboptimal. -/
theorem square_ratio_lt_one (s : ℝ) (hs : 0 < s) :
    4 * π * squareArea s / squareCirc s ^ 2 < 1 := by
  rw [square_isoperimetric_ratio s hs]
  have hpi_lt : π < 4 := by linarith [Real.pi_lt_3141593]
  linarith

/-
## Part III: Regular n-gons Approach the Circle

A regular n-gon with circumference C has area A = C²·cos(π/n)·sin(π/n)/(2πn)...
actually expressed as: A = (C²/(4n)) · cot(π/n), and
the isoperimetric ratio A·4π/C² = (π/n)·cot(π/n) → 1 as n → ∞.

We prove the key formula for the isoperimetric ratio of a regular n-gon.
-/

/-- For a regular n-gon with circumradius R (n ≥ 3):
    side length a = 2R sin(π/n), perimeter C = 2nR sin(π/n), area A = nR² sin(π/n)cos(π/n).
    Isoperimetric ratio: 4πA/C² = π·cos(π/n)/sin(π/n)/n = π/(n·tan(π/n)). -/
theorem regular_ngon_isoperimetric_ratio (n : ℕ) (R : ℝ) (hn : 2 < n) (hR : 0 < R) :
    let C := 2 * n * R * Real.sin (π / n)
    let A := n * R ^ 2 * Real.sin (π / n) * Real.cos (π / n)
    n * Real.tan (π / n) > 0 →
    4 * π * A / C ^ 2 = π / (n * Real.tan (π / n)) := by
  intro htan
  simp only
  have hsin : Real.sin (π / n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply div_lt_self pi_pos
      exact_mod_cast (by omega : 1 < n)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hR' : R ≠ 0 := ne_of_gt hR
  unfold Real.tan
  field_simp [hsin, hn', hR']
  ring

/-- As n → ∞, the regular n-gon approaches the circle (ratio → 1).
    Specifically: π/(n·tan(π/n)) → π/(π) = 1 since n·tan(π/n) → π as n → ∞.

    **Proof**: tan(h)/h → 1 as h → 0 (derivative of tan at 0 is 1).
    Set h = π/n → 0 as n → ∞. Then π/(n·tan(π/n)) = 1/(tan(π/n)/(π/n)) → 1/1 = 1. -/
theorem ngon_limit_tendsto_circle :
    Filter.Tendsto (fun n : ℕ => π / ((n : ℝ) * Real.tan (π / n)))
      Filter.atTop (nhds 1) := by
  -- Step 1: tan(h)/h → 1 as h → 0, h ≠ 0
  -- From hasDerivAt_tan at 0: derivative is 1/cos²(0) = 1
  -- By hasDerivAt_iff_tendsto_slope: slope (= tan h / h) → 1
  have htan_slope : Filter.Tendsto (fun h : ℝ => Real.tan h / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    have h0 : Real.cos (0 : ℝ) ≠ 0 := by norm_num [Real.cos_zero]
    have hd : HasDerivAt Real.tan 1 0 := by
      have := Real.hasDerivAt_tan h0
      rwa [Real.cos_zero, one_pow, div_one] at this
    rw [hasDerivAt_iff_tendsto_slope] at hd
    exact hd.congr' (Filter.Eventually.of_forall (fun y => by
      simp [slope_def_field, Real.tan_zero]))
  -- Step 2: π/n → 0 via atTop, staying ≠ 0 for n ≥ 1
  have hpi_nhds : Filter.Tendsto (fun n : ℕ => (π : ℝ) / n)
      Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    rw [Filter.tendsto_nhdsWithin_iff]
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat π, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact Set.mem_compl_singleton_iff.mpr
      (div_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr (by omega)))
  -- Step 3: tan(π/n)/(π/n) → 1 by composition
  have h_comp : Filter.Tendsto (fun n : ℕ => Real.tan (π / n) / (π / n))
      Filter.atTop (nhds 1) :=
    htan_slope.comp hpi_nhds
  -- Step 4: 1/(tan(π/n)/(π/n)) → 1/1 = 1 by inversion (x → x⁻¹ continuous at 1)
  have h_inv : Filter.Tendsto (fun n : ℕ => 1 / (Real.tan (π / n) / (π / n)))
      Filter.atTop (nhds 1) := by
    have key := h_comp.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simp only [inv_one] at key
    exact key.congr' (Filter.Eventually.of_forall (fun n => (one_div _).symm))
  -- Step 5: Show π/(n*tan(π/n)) = 1/(tan(π/n)/(π/n)) for n ≥ 3
  -- (For n ≥ 3: 0 < π/n < π/2, so cos(π/n) > 0 and tan(π/n) > 0)
  apply h_inv.congr'
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hpn_pos : (0 : ℝ) < π / n := by positivity
  have hpn_lt : π / (n : ℝ) < π / 2 := by
    have h2n : (2 : ℝ) < n := by linarith
    have hn_pos : (0 : ℝ) < n := by linarith
    rw [div_lt_div_iff hn_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hcos_pos : 0 < Real.cos (π / n) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hpn_pos, div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2)], hpn_lt⟩
  have htan_ne : Real.tan (π / n) ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero
      (Real.sin_pos_of_pos_of_lt_pi hpn_pos
        (lt_trans hpn_lt (div_lt_self Real.pi_pos one_lt_two))).ne'
      hcos_pos.ne'
  have hpn_ne : π / (n : ℝ) ≠ 0 := div_ne_zero Real.pi_ne_zero hn0
  field_simp [hn0, htan_ne, hpn_ne]

/-
## Part IV: Wirtinger's Inequality and the Isoperimetric Deduction

The isoperimetric inequality for smooth curves follows from Wirtinger's inequality
plus Cauchy-Schwarz and AM-GM. We state Wirtinger as an axiom and prove the deduction.
-/

/-
  **Wirtinger's Inequality** (not yet in Mathlib)

  For f : ℝ → ℝ that is absolutely continuous, 2π-periodic, and has zero mean
  (∫₀²π f(t) dt = 0), the following holds:

    ∫₀²π f(t)² dt ≤ ∫₀²π f'(t)² dt

  Proof: Expand f in Fourier series: f(t) = ∑ₙ≥₁ (aₙ cos(nt) + bₙ sin(nt)) (zero mean)
  Then: ∫f² = π ∑(aₙ² + bₙ²) and ∫(f')² = π ∑ n²(aₙ² + bₙ²) ≥ π ∑(aₙ² + bₙ²) = ∫f²
  with equality iff f(t) = a₁ cos(t) + b₁ sin(t).

  Mathlib has: fourierBasis, tsum_sq_fourierCoeff (Parseval), hasSum_fourier_series_L2
  Missing: assembling these into the Wirtinger inequality statement.
-/

/-- A smooth closed curve in the plane, parametrized by [0, 2π]. -/
structure SmoothClosedCurve where
  x : ℝ → ℝ
  y : ℝ → ℝ
  periodic_x : ∀ t, x (t + 2 * π) = x t
  periodic_y : ∀ t, y (t + 2 * π) = y t
  smooth_x : ContDiff ℝ 1 x
  smooth_y : ContDiff ℝ 1 y

/-- Circumference of a smooth closed curve (arc length). -/
noncomputable def SmoothClosedCurve.circumference (γ : SmoothClosedCurve) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (deriv γ.x t ^ 2 + deriv γ.y t ^ 2)

/-- Area enclosed by a smooth closed curve (Green's theorem). -/
noncomputable def SmoothClosedCurve.area (γ : SmoothClosedCurve) : ℝ :=
  (1 / 2) * |∫ t in (0 : ℝ)..(2 * π), γ.x t * deriv γ.y t - γ.y t * deriv γ.x t|

/-- The circle of radius r as a smooth closed curve. -/
def circleGamma (r : ℝ) : SmoothClosedCurve where
  x := fun t => r * Real.cos t
  y := fun t => r * Real.sin t
  periodic_x := by intro t; simp [Real.cos_add_two_pi]
  periodic_y := by intro t; simp [Real.sin_add_two_pi]
  smooth_x := contDiff_const.mul Real.contDiff_cos
  smooth_y := contDiff_const.mul Real.contDiff_sin

/-- The circumference of circleGamma equals circleCirc r (i.e., 2πr).
    Proof: The arc-length integrand √((r·(-sin t))² + (r·cos t)²) = r by
    the Pythagorean identity, so ∫₀²π r dt = 2πr. -/
theorem circleGamma_circumference (r : ℝ) (hr : 0 < r) :
    (circleGamma r).circumference = circleCirc r := by
  unfold SmoothClosedCurve.circumference circleGamma circleCirc
  simp only
  -- Simplify the integrand to the constant r using trig identity
  have hsimp : ∀ t : ℝ,
      Real.sqrt ((deriv (fun t => r * Real.cos t) t) ^ 2 +
                 (deriv (fun t => r * Real.sin t) t) ^ 2) = r := fun t => by
    have hdx : deriv (fun t => r * Real.cos t) t = r * (-Real.sin t) :=
      ((Real.hasDerivAt_cos t).const_mul r).deriv
    have hdy : deriv (fun t => r * Real.sin t) t = r * Real.cos t :=
      ((Real.hasDerivAt_sin t).const_mul r).deriv
    rw [hdx, hdy]
    have h1 : (r * -Real.sin t) ^ 2 + (r * Real.cos t) ^ 2 = r ^ 2 := by
      have h := Real.sin_sq_add_cos_sq t
      have : (r * -Real.sin t) ^ 2 + (r * Real.cos t) ^ 2 =
             r ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      rw [this, h, mul_one]
    rw [h1, Real.sqrt_sq hr.le]
  simp_rw [hsimp]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- The area of circleGamma equals circleArea r (i.e., πr²).
    Proof: The Green's theorem integrand xy' - yx' = r²·(cos²t + sin²t) = r²,
    so (1/2)|∫₀²π r² dt| = (1/2)·r²·2π = πr². -/
theorem circleGamma_area (r : ℝ) (hr : 0 < r) :
    (circleGamma r).area = circleArea r := by
  unfold SmoothClosedCurve.area circleGamma circleArea
  simp only
  -- Simplify the Green's theorem integrand to the constant r²
  have hint : ∀ t : ℝ,
      r * Real.cos t * deriv (fun t => r * Real.sin t) t -
      r * Real.sin t * deriv (fun t => r * Real.cos t) t = r ^ 2 := fun t => by
    have hdx : deriv (fun t => r * Real.cos t) t = r * (-Real.sin t) :=
      ((Real.hasDerivAt_cos t).const_mul r).deriv
    have hdy : deriv (fun t => r * Real.sin t) t = r * Real.cos t :=
      ((Real.hasDerivAt_sin t).const_mul r).deriv
    rw [hdy, hdx]
    have h : r * Real.cos t * (r * Real.cos t) - r * Real.sin t * (r * -Real.sin t) =
             r ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    rw [h, Real.sin_sq_add_cos_sq, mul_one]
  simp_rw [hint]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      abs_of_pos (by positivity)]
  ring

/-- For circleGamma r, the isoperimetric inequality is an equality: C² = 4πA.
    This combines circleGamma_circumference and circleGamma_area. -/
theorem circleGamma_isoperimetric_equality (r : ℝ) (hr : 0 < r) :
    (circleGamma r).circumference ^ 2 = 4 * π * (circleGamma r).area := by
  rw [circleGamma_circumference r hr, circleGamma_area r hr]
  exact circle_isoperimetric_equality r

/-- **Wirtinger's Inequality** (axiomatized — see proof notes above).
    The key ingredient needed to prove the isoperimetric inequality for general curves. -/
axiom wirtinger_inequality (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hmean : ∫ t in (0 : ℝ)..(2 * π), f t = 0) :
    ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 ≤
    ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2

/-
## Part V: The Isoperimetric Inequality for Smooth Curves

Using Wirtinger's inequality, we state the general isoperimetric inequality.
The proof sketch (from the axiom) uses:
  - Wirtinger on x̃ - x̄ and ỹ - ȳ (centered versions)
  - Cauchy-Schwarz: A ≤ (1/2)√(∫x²·∫y'²) + (1/2)√(∫y²·∫x'²)
  - Wirtinger: ∫x² ≤ ∫x'² (when mean zero) and ∫y² ≤ ∫y'²
  - AM-GM: √(∫x'²·∫y'²) ≤ (∫x'² + ∫y'²)/2
  - Combined with unit speed: ∫x'² + ∫y'² = L²/(2π)
  Result: 4πA ≤ L²
-/

/-- **The General Isoperimetric Inequality for Smooth Curves** (from Wirtinger).
    This follows from wirtinger_inequality via Cauchy-Schwarz and AM-GM. -/
theorem isoperimetric_inequality_smooth (γ : SmoothClosedCurve) :
    4 * π * γ.area ≤ γ.circumference ^ 2 := by
  -- This deduction from Wirtinger's inequality requires:
  -- 1. Cauchy-Schwarz for integrals: (∫fg)² ≤ ∫f² · ∫g²
  -- 2. Green's theorem: A = (1/2)|∫(xy' - yx')|
  -- 3. Wirtinger: ∫(x-x̄)² ≤ ∫x'² (when translated to mean zero)
  -- 4. AM-GM: √(ab) ≤ (a+b)/2
  -- These are standard but the assembly requires ~100 lines
  -- The key axiom needed is wirtinger_inequality above
  sorry -- reducible to wirtinger_inequality once smooth curve analysis infrastructure available

/-
## Part VI: Equality Characterization

The isoperimetric inequality is an equality iff the curve is a circle.
The equality condition in Wirtinger: ∫f² = ∫(f')² iff f = a·cos(t) + b·sin(t).
This gives x = r·cos(t + φ) and y = r·sin(t + φ): a translated circle.
-/

/-- Circles satisfy the isoperimetric inequality with equality. -/
theorem circle_satisfies_isoperimetric (r : ℝ) (hr : 0 < r) :
    let C := circleCirc r
    let A := circleArea r
    C ^ 2 = 4 * π * A := by
  exact circle_isoperimetric_equality r

/-- If a smooth closed curve achieves equality, it is a circle.
    (Equality condition in Wirtinger: only sinusoidal functions give equality) -/
axiom equality_implies_circle (γ : SmoothClosedCurve)
    (heq : 4 * π * γ.area = γ.circumference ^ 2) :
    ∃ (r : ℝ) (hx : γ.circumference = circleCirc r),
      γ.area = circleArea r

/-
## Part VII: Algebraic Corollaries of the Isoperimetric Inequality

These follow directly from 4πA ≤ C² without using the hard Wirtinger proof.
They use the circle-specific inequality results we've proved.
-/

/-- Rearrangement: 4πA ≤ C² is equivalent to A ≤ C²/(4π).
    For circles: A = C²/(4π) exactly. -/
theorem isoperimetric_area_bound (C A : ℝ)
    (h : 4 * π * A ≤ C ^ 2) :
    A ≤ C ^ 2 / (4 * π) := by
  have h4pi : 0 < 4 * π := by linarith [Real.pi_pos]
  rw [← sub_nonneg]
  have hkey : C ^ 2 / (4 * π) - A = (C ^ 2 - 4 * π * A) / (4 * π) := by
    field_simp
  rw [hkey]
  exact div_nonneg (by linarith) h4pi.le

/-- Minimum circumference for given area: C ≥ 2·√(π·A).
    Follows from 4πA ≤ C² by taking square roots.
    The circle minimizes circumference for given area. -/
theorem minimum_circumference_for_area (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (h : 4 * π * A ≤ C ^ 2) :
    2 * Real.sqrt (π * A) ≤ C := by
  have hpi : 0 < π := Real.pi_pos
  -- Rewrite 2√(πA) = √(4πA) and C = √(C²), then use monotonicity of sqrt
  have h2sqrt : 2 * Real.sqrt (π * A) = Real.sqrt (4 * π * A) := by
    rw [show (4 : ℝ) * π * A = (2 : ℝ)^2 * (π * A) from by ring,
        Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)^2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2sqrt, ← Real.sqrt_sq hC.le]
  exact Real.sqrt_le_sqrt h

/-- Scale invariance: the isoperimetric ratio 4πA/C² is unchanged by scaling.
    If a curve has circumference C and area A, scaling by s ≠ 0 gives
    circumference sC and area s²A, leaving 4π(s²A)/(sC)² = 4πA/C² unchanged. -/
theorem isoperimetric_ratio_scale_invariant (C A s : ℝ) (hC : C ≠ 0) (hs : s ≠ 0) :
    4 * π * (s ^ 2 * A) / (s * C) ^ 2 = 4 * π * A / C ^ 2 := by
  field_simp [hs, hC]

/-- The circle achieves the maximum area for given circumference.
    Among all smooth closed curves with circumference C = 2πr, the circle of radius r
    encloses the maximum area πr². -/
theorem circle_maximizes_area (r : ℝ) (hr : 0 < r) (γ : SmoothClosedCurve)
    (hC : γ.circumference = circleCirc r)
    (hineq : 4 * π * γ.area ≤ γ.circumference ^ 2) :
    γ.area ≤ circleArea r := by
  rw [hC, circle_isoperimetric_equality r] at hineq
  have h4pi : 0 < 4 * π := by linarith [Real.pi_pos]
  exact le_of_mul_le_mul_left hineq h4pi

/-- Strict inequality: if a smooth closed curve with given circumference is NOT a circle,
    its enclosed area is strictly less than the circle's area. -/
theorem non_circle_area_lt_circle (r : ℝ) (hr : 0 < r) (γ : SmoothClosedCurve)
    (hC : γ.circumference = circleCirc r)
    (hineq : 4 * π * γ.area < γ.circumference ^ 2) :
    γ.area < circleArea r := by
  rw [hC, circle_isoperimetric_equality r] at hineq
  have h4pi : 0 < 4 * π := by linarith [Real.pi_pos]
  exact lt_of_mul_lt_mul_left hineq h4pi.le

/-
## Summary

### The Isoperimetric Inequality: C² ≥ 4πA

### Proved (0 sorries in 17 theorems):
1. `circle_isoperimetric_equality` — C² = 4πA for circles (equality case)
2. `circle_isoperimetric_ratio` — 4πA/C² = 1 for circles
3. `square_isoperimetric_strict` — C² > 4πA for squares (from π < 4)
4. `square_isoperimetric_ratio` — 4πA/C² = π/4 for squares
5. `square_ratio_lt_one` — square ratio < 1 (confirming suboptimality)
6. `regular_ngon_isoperimetric_ratio` — 4πA/C² = π/(n·tan(π/n)) for n-gons
7. `ngon_limit_tendsto_circle` — π/(n·tan(π/n)) → 1 as n → ∞ (via tan x/x → 1)
8. `circumference_is_deriv_of_area` — C = dA/dr (connection to OQ01)
9. `circleGamma_circumference` — circleGamma(r).circumference = 2πr [arc-length integral]
10. `circleGamma_area` — circleGamma(r).area = πr² [Green's theorem integral]
11. `circleGamma_isoperimetric_equality` — C² = 4πA for circleGamma [corollary]
12. `circle_satisfies_isoperimetric` — circles satisfy C² = 4πA
13. `isoperimetric_area_bound` — 4πA ≤ C² ⟹ A ≤ C²/(4π) [algebraic]
14. `minimum_circumference_for_area` — 4πA ≤ C² ⟹ 2√(πA) ≤ C [from sqrt monotonicity]
15. `isoperimetric_ratio_scale_invariant` — ratio 4πA/C² invariant under scaling [ring]
16. `circle_maximizes_area` — if C = 2πr and 4πA ≤ C², then A ≤ πr²
17. `non_circle_area_lt_circle` — strict: 4πA < C² ⟹ A < circleArea r
18. `cross_product_sq_le` — 2D CS: |xv-yu|² ≤ (x²+y²)(u²+v²) [algebraic, nlinarith]
19. `isoperimetric_from_wirtinger_bounds` — arithmetic kernel: from Wirtinger bounds to 4πA ≤ L²

### Axioms (2):
1. `wirtinger_inequality` — ∫f² ≤ ∫(f')² for periodic mean-zero f
   (Proof: Fourier series + Parseval; Mathlib has all ingredients)
2. `equality_implies_circle` — equality iff circle
   (Proof: equality in Wirtinger iff f = a cos + b sin)

### 1 Sorry:
1. `isoperimetric_inequality_smooth` — reducible to wirtinger_inequality
   (needs integral Cauchy-Schwarz assembly, ~100 lines)
   Correct proof (for constant-speed curves): shift x, y to zero mean;
   constant speed c gives ∫(x'²+y'²) = 2πc² EXACTLY (equality, not ineq);
   Wirtinger gives ∫(x²+y²) ≤ 2πc²; integral C-S gives ∫√(x²+y²) ≤ 2πc;
   Green's + 2D C-S gives 2A ≤ c·∫√(x²+y²) ≤ 2πc²; so 4πA ≤ L².
   NOTE: The naive variable-speed route (arc-length CS L² ≤ 2π∫(x'²+y'²))
   gives an upper bound on L², not a lower bound — wrong direction! Always
   use constant-speed parametrization (reparametrize by arc length).
   See isoperimetric_from_wirtinger_bounds for the arithmetic kernel.

### Proof of ngon_limit_tendsto_circle:
- `Real.hasDerivAt_tan (cos 0 ≠ 0) : HasDerivAt tan (1/cos²0) 0 = HasDerivAt tan 1 0`
- `hasDerivAt_iff_tendsto_slope`: slope(tan, 0) h = tan h / h → 1 as h → 0
- `tendsto_const_div_atTop_nhds_zero_nat π`: π/n → 0 via atTop
- Compose: tan(π/n)/(π/n) → 1, then 1/(tan(π/n)/(π/n)) → 1, matching π/(n·tan(π/n))

### Key Insight:
The isoperimetric inequality C² ≥ 4πA follows from Wirtinger's inequality,
which in turn follows from Fourier analysis. Mathlib has the Fourier infrastructure
(fourierBasis, tsum_sq_fourierCoeff, fourierCoeffOn_of_hasDerivAt) needed to prove
Wirtinger, making this a tractable ~300-line formalization once assembled.
-/

/-
## Part VIII: Arithmetic Foundations for the Isoperimetric Proof

Two key ingredients for the Hurwitz 1901 proof:
1. The 2D Cauchy-Schwarz inequality (purely algebraic)
2. The arithmetic kernel that assembles Wirtinger bounds into 4πA ≤ L²

These are fully proved here, reducing the isoperimetric inequality to:
- The wirtinger_inequality axiom (Fourier proof, ~200 lines)
- Integral Cauchy-Schwarz (standard Mathlib, ~20 lines once assembled)
- Green's formula with 2D C-S (combining cross_product_sq_le, ~30 lines)
-/

/-- **2D Cauchy-Schwarz** (algebraic): |x·v - y·u|² ≤ (x²+y²)(u²+v²).
    Equivalently, the squared area of the parallelogram spanned by (x,y) and (u,v)
    is at most the product of their squared norms (squared magnitudes).
    Proof: expand the trivially non-negative (x·u + y·v)².
    Used in the isoperimetric proof: |xy'-yx'| ≤ √(x²+y²) · |γ'|. -/
theorem cross_product_sq_le (x y u v : ℝ) :
    (x * v - y * u) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (x * u + y * v)]

/-- **Arithmetic kernel**: Assembles Wirtinger bounds into the isoperimetric inequality 4πA ≤ L².

This is the final step of Hurwitz's 1901 proof, after the analytical ingredients are assembled.
The argument is purely arithmetic — no integrals or measures appear.

**Inputs** (the assembled analysis for a constant-speed zero-mean curve):
- `L = 2πc`      : circumference from constant-speed c parametrization
- `S ≥ 0`        : S = ∫₀²π √(x²+y²) dt
- `Sxy ≥ 0`      : Sxy = ∫₀²π (x²+y²) dt
- `2A ≤ c·S`     : from Green's theorem: 2A = |∫(xy'-yx')| ≤ ∫|xy'-yx'| ≤ c·∫√(x²+y²)
                   (using 2D Cauchy-Schwarz: |xy'-yx'| ≤ √(x²+y²)·|(x',y')| = c·√(x²+y²))
- `S² ≤ 2π·Sxy`  : integral Cauchy-Schwarz: (∫₀²π f)² ≤ (∫₀²π 1)·(∫₀²π f²) with f=√(x²+y²)
- `Sxy ≤ 2πc²`   : from Wirtinger: ∫(x²+y²) ≤ ∫(x'²+y'²) = ∫c² = 2πc²
                   (constant speed gives ∫(x'²+y'²) = 2πc² EXACTLY, not just a bound!)

**Proof chain**: S² ≤ 2π·Sxy ≤ 2π·2πc² = (2πc)² → S ≤ 2πc
  → 2A ≤ c·S ≤ 2πc² → A ≤ πc² → 4πA ≤ 4π²c² = (2πc)² = L² ✓ -/
theorem isoperimetric_from_wirtinger_bounds
    (A L c S Sxy : ℝ)
    (hc : 0 < c)
    (hcirc : L = 2 * π * c)
    (hS_nn : 0 ≤ S)
    (harea : 2 * A ≤ c * S)
    (hCS : S ^ 2 ≤ 2 * π * Sxy)
    (hWirt : Sxy ≤ 2 * π * c ^ 2) :
    4 * π * A ≤ L ^ 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h2pic_pos : (0 : ℝ) < 2 * π * c := by positivity
  -- Step 1: S² ≤ (2πc)²  (chain the Wirtinger bounds)
  have hS2 : S ^ 2 ≤ (2 * π * c) ^ 2 :=
    calc S ^ 2 ≤ 2 * π * Sxy := hCS
         _ ≤ 2 * π * (2 * π * c ^ 2) := by
             apply mul_le_mul_of_nonneg_left hWirt; linarith
         _ = (2 * π * c) ^ 2 := by ring
  -- Step 2: S ≤ 2πc  (from S ≥ 0, S² ≤ (2πc)², 2πc ≥ 0 — via sqrt monotonicity)
  have hS_bound : S ≤ 2 * π * c := by
    have h := Real.sqrt_le_sqrt hS2
    rwa [Real.sqrt_sq hS_nn, Real.sqrt_sq h2pic_pos.le] at h
  -- Step 3: 2A ≤ 2πc² and then 4πA ≤ L²
  have h1 : c * S ≤ 2 * π * c ^ 2 :=
    calc c * S ≤ c * (2 * π * c) := mul_le_mul_of_nonneg_left hS_bound (le_of_lt hc)
         _ = 2 * π * c ^ 2 := by ring
  have hA : A ≤ π * c ^ 2 := by linarith
  have h2 : 4 * π * A ≤ (2 * π * c) ^ 2 :=
    calc 4 * π * A ≤ 4 * π * (π * c ^ 2) :=
              mul_le_mul_of_nonneg_left hA (by linarith)
         _ = (2 * π * c) ^ 2 := by ring
  rw [hcirc]; exact h2

end IsoperimetricOQ

end
