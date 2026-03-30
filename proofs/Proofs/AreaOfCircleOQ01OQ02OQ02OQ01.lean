/-
  Isoperimetric Inequality: Assembly from IBP + Wirtinger + Parseval
  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01

  This file proves the isoperimetric inequality L² ≥ 4πA for smooth closed
  curves, making the classical Hurwitz (1901) proof chain fully explicit:

    Parseval (Mathlib) + IBP ⟹ Wirtinger ⟹ Isoperimetric inequality

  Architecture:
  - Part I: IBP for Fourier coefficients (proved from Mathlib, 0 sorries)
  - Part II: Wirtinger's inequality (1 sorry — Parseval bridge to real integrals)
  - Part III: Isoperimetric inequality for nice curves (proved from Wirtinger)

  Total: 1 sorry (the Parseval bridge from Mathlib's tsum_sq_fourierCoeff on
  AddCircle(2π) to interval integrals on [0,2π]). All other steps fully proved.

  References:
  - Hurwitz (1901): "Sur quelques applications géométriques des séries de Fourier"
  - AreaOfCircleOQ01OQ02OQ02.lean: IBP formula (verified, 0 sorries)
  - AreaOfCircleOQ01OQ03.lean: Full isoperimetric proof (3 sorries, 52 theorems)
  - Mathlib: tsum_sq_fourierCoeff, fourierCoeffOn_of_hasDerivAt
-/

import Mathlib

open Real Complex MeasureTheory Filter Topology

noncomputable section

namespace IsoperimetricAssembly

-- ============================================================
-- PART I: Integration by Parts for Fourier Coefficients
-- ============================================================

/-- Chain rule: HasDerivAt (ofReal ∘ f) ((ofReal ∘ deriv f) x) x for C¹ real f.
    Uses ContinuousLinearMap.hasDerivAt for ofRealCLM composed via HasDerivAt.scomp. -/
theorem hasDerivAt_ofReal_comp (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : ℝ) :
    HasDerivAt (ofReal ∘ f) ((ofReal ∘ deriv f) x) x := by
  have hd : HasDerivAt f (deriv f x) x := (hf.differentiable le_rfl x).hasDerivAt
  have hg : HasDerivAt (⇑ofRealCLM) (ofRealCLM 1) (f x) :=
    ContinuousLinearMap.hasDerivAt ofRealCLM
  have h := hg.scomp x hd
  convert h using 1
  simp [Function.comp, ofReal_one, mul_one]

/-- **IBP for Fourier coefficients**: ĉₙ(f') = in · ĉₙ(f).

    For a C¹ function f with period 2π and n ≠ 0, the Fourier coefficient of
    the derivative equals i·n times the Fourier coefficient of f.

    Proof: Apply Mathlib's fourierCoeffOn_of_hasDerivAt. The boundary term
    f(2π) - f(0) vanishes by periodicity, leaving a clean algebraic identity.

    This is the first ingredient of the Hurwitz chain: differentiation in the
    time domain corresponds to multiplication by in in the frequency domain. -/
theorem ibp_fourier (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv f) n =
    I * ↑n * fourierCoeffOn hab (ofReal ∘ f) n := by
  -- Derivative hypothesis for Mathlib's IBP
  have hderiv : ∀ x ∈ Set.uIcc 0 (2 * π),
      HasDerivAt (ofReal ∘ f) ((ofReal ∘ deriv f) x) x :=
    fun x _ => hasDerivAt_ofReal_comp f hf x
  -- Integrability of the derivative
  have hint : IntervalIntegrable (ofReal ∘ deriv f) volume 0 (2 * π) :=
    (continuous_ofReal.comp (hf.continuous_deriv le_rfl)).intervalIntegrable 0 (2 * π)
  -- Apply Mathlib's IBP formula for Fourier coefficients
  have hibp := fourierCoeffOn_of_hasDerivAt hab hn hderiv hint
  -- Periodicity kills the boundary term: f(2π) - f(0) = 0
  have hfp : f (2 * π) = f 0 := by have h := hperiod 0; rwa [zero_add] at h
  -- Simplify and close with algebra
  rw [hibp]
  simp only [Function.comp_apply, hfp, sub_self, mul_zero, zero_sub, ofReal_zero, sub_zero]
  have h1 : (↑π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt pi_pos)
  have h2 : (I : ℂ) ≠ 0 := I_ne_zero
  have h3 : (↑n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  field_simp; push_cast; ring

/-- Norm consequence of IBP: ‖ĉₙ(f')‖ = |n| · ‖ĉₙ(f)‖.
    In the frequency domain, differentiation scales each coefficient by |n|. -/
theorem norm_ibp_fourier (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖ =
    |↑n| * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [ibp_fourier f hf hperiod hab n hn]
  simp [map_mul, norm_mul, Complex.abs_I, one_mul, mul_assoc]

-- ============================================================
-- PART II: Wirtinger's Inequality
-- ============================================================

/-- **Wirtinger's inequality** (Fourier-analytic proof):
    For C¹, 2π-periodic, mean-zero f: ∫₀²π f(t)² dt ≤ ∫₀²π f'(t)² dt.

    **Proof chain** (Hurwitz 1901):
    1. Parseval: ∫f² = 2π · Σₙ ‖ĉₙ(f)‖², ∫(f')² = 2π · Σₙ ‖ĉₙ(f')‖²
    2. IBP (ibp_fourier): ‖ĉₙ(f')‖ = |n| · ‖ĉₙ(f)‖, so ‖ĉₙ(f')‖² = n² · ‖ĉₙ(f)‖²
    3. Mean zero: ĉ₀(f) = (1/(2π))∫f = 0
    4. For n ≠ 0: n² ≥ 1, so n² · ‖ĉₙ‖² ≥ ‖ĉₙ‖²
    5. Sum: Σₙ n² · ‖ĉₙ‖² ≥ Σₙ ‖ĉₙ‖², hence ∫(f')² ≥ ∫f²

    **Sorry**: The Parseval bridge — converting Mathlib's tsum_sq_fourierCoeff on
    AddCircle(2π) with Haar measure to interval integrals on [0, 2π] with Lebesgue
    measure — is technically involved (~100 lines of measure-theoretic bookkeeping).
    The mathematical content is standard; the formalization gap is the measure bridge.
    See parseval_AddCircle_lift in AreaOfCircleOQ01OQ03.lean for the full bridge. -/
theorem wirtinger_inequality (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hmean : ∫ t in (0 : ℝ)..(2 * π), f t = 0) :
    ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 ≤
    ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2 := by
  sorry

-- ============================================================
-- PART III: The Isoperimetric Inequality
-- ============================================================

-- A smooth closed curve with constant speed and zero mean.
-- These "nice" properties are achieved by arc-length reparametrization
-- (constant speed) and translation by the centroid (zero mean).
-- Working with nice curves avoids the arc-length reparametrization sorry.

/-- A smooth closed curve in the plane with constant speed and zero mean. -/
structure NiceCurve where
  x : ℝ → ℝ
  y : ℝ → ℝ
  periodic_x : ∀ t, x (t + 2 * π) = x t
  periodic_y : ∀ t, y (t + 2 * π) = y t
  smooth_x : ContDiff ℝ 1 x
  smooth_y : ContDiff ℝ 1 y
  c : ℝ
  c_pos : 0 < c
  const_speed : ∀ t, deriv x t ^ 2 + deriv y t ^ 2 = c ^ 2
  mean_x_zero : ∫ t in (0 : ℝ)..(2 * π), x t = 0
  mean_y_zero : ∫ t in (0 : ℝ)..(2 * π), y t = 0

/-- Circumference of a nice curve (arc length integral). -/
noncomputable def NiceCurve.circumference (γ : NiceCurve) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (deriv γ.x t ^ 2 + deriv γ.y t ^ 2)

/-- Enclosed area of a nice curve (Green's theorem). -/
noncomputable def NiceCurve.area (γ : NiceCurve) : ℝ :=
  (1 / 2) * |∫ t in (0 : ℝ)..(2 * π), γ.x t * deriv γ.y t - γ.y t * deriv γ.x t|

/-- Circumference of a constant-speed-c curve: ∫₀²π √(c²) dt = 2πc. -/
theorem NiceCurve.circumference_eq (γ : NiceCurve) :
    γ.circumference = 2 * π * γ.c := by
  unfold NiceCurve.circumference
  simp_rw [γ.const_speed, Real.sqrt_sq γ.c_pos.le]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

-- ============================================================
-- Step 1: Wirtinger bound on ∫(x² + y²)
-- ============================================================

/-- Wirtinger bound: ∫₀²π (x² + y²) ≤ 2πc².
    Apply Wirtinger to x and y separately, then use constant speed. -/
theorem NiceCurve.wirtinger_bound (γ : NiceCurve) :
    ∫ t in (0 : ℝ)..(2 * π), (γ.x t ^ 2 + γ.y t ^ 2) ≤ 2 * π * γ.c ^ 2 := by
  -- Apply Wirtinger to x and y
  have wx := wirtinger_inequality γ.x γ.smooth_x γ.periodic_x γ.mean_x_zero
  have wy := wirtinger_inequality γ.y γ.smooth_y γ.periodic_y γ.mean_y_zero
  -- Integrability
  have hx2 := (γ.smooth_x.continuous.pow 2).intervalIntegrable (a := (0 : ℝ)) (b := 2 * π)
  have hy2 := (γ.smooth_y.continuous.pow 2).intervalIntegrable (a := (0 : ℝ)) (b := 2 * π)
  have hdx2 := ((γ.smooth_x.continuous_deriv le_rfl).pow 2).intervalIntegrable
    (a := (0 : ℝ)) (b := 2 * π)
  have hdy2 := ((γ.smooth_y.continuous_deriv le_rfl).pow 2).intervalIntegrable
    (a := (0 : ℝ)) (b := 2 * π)
  -- ∫(x²+y²) = ∫x² + ∫y² ≤ ∫(x')² + ∫(y')² = ∫(x'²+y'²) = 2πc²
  rw [intervalIntegral.integral_add hx2 hy2]
  have h_sum := add_le_add wx wy
  rw [← intervalIntegral.integral_add hdx2 hdy2] at h_sum
  have h_eq : (fun t => deriv γ.x t ^ 2 + deriv γ.y t ^ 2) = fun _ => γ.c ^ 2 :=
    funext γ.const_speed
  rw [h_eq, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h_sum
  linarith

-- ============================================================
-- Step 2: 2D Cauchy-Schwarz (algebraic)
-- ============================================================

/-- 2D Cauchy-Schwarz: |xv - yu|² ≤ (x² + y²)(u² + v²).
    The squared area of a parallelogram ≤ product of squared side lengths. -/
theorem cross_sq_le (x y u v : ℝ) :
    (x * v - y * u) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (x * u + y * v)]

-- ============================================================
-- Step 3: Integral Cauchy-Schwarz
-- ============================================================

/-- Integral Cauchy-Schwarz on [0, 2π]: (∫f)² ≤ 2π · ∫f².
    Proof: discriminant method — ∫(αf-1)² ≥ 0 for all α implies
    the discriminant (∫f)² - 2π·∫f² ≤ 0 of the quadratic in α. -/
theorem integral_cauchy_schwarz (f : ℝ → ℝ)
    (hf_int : IntervalIntegrable f MeasureSpace.volume 0 (2 * π))
    (hf2_int : IntervalIntegrable (fun t => f t ^ 2) MeasureSpace.volume 0 (2 * π)) :
    (∫ t in (0 : ℝ)..(2 * π), f t) ^ 2 ≤
    2 * π * ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 := by
  set I' := ∫ t in (0 : ℝ)..(2 * π), f t
  set J := ∫ t in (0 : ℝ)..(2 * π), f t ^ 2
  -- For all α: ∫(αf - 1)² ≥ 0 gives α²J - 2αI' + 2π ≥ 0
  have hQ : ∀ α : ℝ, 0 ≤ α ^ 2 * J - 2 * α * I' + 2 * π := by
    intro α
    have h_nn : 0 ≤ ∫ t in (0 : ℝ)..(2 * π), (α * f t - 1) ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith [pi_pos]) (fun t _ => sq_nonneg _)
    have hexp : ∀ t, (α * f t - 1) ^ 2 = α ^ 2 * f t ^ 2 + (-2 * α * f t + 1) := by
      intro t; ring
    simp_rw [hexp] at h_nn
    rw [intervalIntegral.integral_add (hf2_int.const_mul _)
        ((hf_int.const_mul _).add intervalIntegrable_const)] at h_nn
    rw [intervalIntegral.integral_add (hf_int.const_mul _) intervalIntegrable_const] at h_nn
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
               smul_eq_mul, sub_zero] at h_nn
    linarith
  -- J ≥ 0 (integral of squares)
  have hJ : 0 ≤ J :=
    intervalIntegral.integral_nonneg (by linarith [pi_pos]) (fun t _ => sq_nonneg _)
  by_cases hJ0 : J = 0
  · -- J = 0: show I' = 0 by evaluating hQ at α = (π+1)/I'
    suffices hI0 : I' = 0 by simp [hI0, hJ0]
    by_contra hI_ne
    have h := hQ ((π + 1) / I')
    rw [show ((π + 1) / I') ^ 2 * J = 0 from by rw [hJ0, mul_zero], zero_sub] at h
    have : 2 * ((π + 1) / I') * I' = 2 * (π + 1) := by
      rw [mul_assoc, div_mul_cancel₀ _ hI_ne]
    linarith
  · -- J > 0: evaluate at α = I'/J, multiply by J
    have hJ_pos : 0 < J := lt_of_le_of_ne hJ (Ne.symm hJ0)
    have h1 := hQ (I' / J)
    have h2 := mul_le_mul_of_nonneg_right h1 hJ_pos.le
    simp only [zero_mul] at h2
    have key : ((I' / J) ^ 2 * J - 2 * (I' / J) * I' + 2 * π) * J =
               -(I' ^ 2) + 2 * π * J := by field_simp; ring
    rw [key] at h2; linarith

-- ============================================================
-- Step 4: Area bound from Green's theorem + Cauchy-Schwarz
-- ============================================================

/-- For a constant-speed-c curve: 2 · area ≤ c · ∫₀²π √(x² + y²).
    From Green's theorem + 2D Cauchy-Schwarz + constant speed. -/
theorem NiceCurve.area_bound (γ : NiceCurve) :
    2 * γ.area ≤
    γ.c * ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2) := by
  unfold NiceCurve.area
  have hpi_pos : (0 : ℝ) < 2 * π := by positivity
  rw [show (2 : ℝ) * ((1 / 2) * |∫ t in (0 : ℝ)..(2 * π),
    γ.x t * deriv γ.y t - γ.y t * deriv γ.x t|) =
    |∫ t in (0 : ℝ)..(2 * π),
    γ.x t * deriv γ.y t - γ.y t * deriv γ.x t| from by ring]
  -- Pointwise: |xy' - yx'| ≤ c · √(x² + y²) via 2D Cauchy-Schwarz
  have h_pw : ∀ t, |γ.x t * deriv γ.y t - γ.y t * deriv γ.x t| ≤
      γ.c * Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2) := by
    intro t
    have hCS := cross_sq_le (γ.x t) (γ.y t) (deriv γ.x t) (deriv γ.y t)
    rw [γ.const_speed t] at hCS
    have hsum_nn : 0 ≤ γ.x t ^ 2 + γ.y t ^ 2 := by positivity
    -- |xy'-yx'|² ≤ (x²+y²)·c² = (c·√(x²+y²))²
    have h_sq : (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t) ^ 2 ≤
        (γ.c * Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hsum_nn]
      linarith [mul_comm (γ.x t ^ 2 + γ.y t ^ 2) (γ.c ^ 2)]
    -- From a² ≤ b² and b ≥ 0: |a| ≤ b
    have hb_nn : 0 ≤ γ.c * Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2) := by positivity
    rwa [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hb_nn,
         Real.sqrt_le_sqrt]
  -- Derivative continuity
  have hdx_cont : Continuous (deriv γ.x) := γ.smooth_x.continuous_deriv le_rfl
  have hdy_cont : Continuous (deriv γ.y) := γ.smooth_y.continuous_deriv le_rfl
  -- Integrability
  have hf_int : IntervalIntegrable
      (fun t => γ.x t * deriv γ.y t - γ.y t * deriv γ.x t) volume 0 (2 * π) :=
    ((γ.smooth_x.continuous.mul hdy_cont).sub
     (γ.smooth_y.continuous.mul hdx_cont)).intervalIntegrable _ _
  have hg_int : IntervalIntegrable (fun t => γ.c * Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2))
      volume 0 (2 * π) :=
    (continuous_const.mul ((γ.smooth_x.continuous.pow 2).add
      (γ.smooth_y.continuous.pow 2)).sqrt).intervalIntegrable _ _
  -- Upper bound: ∫(xy'-yx') ≤ c·∫√(x²+y²)
  have h_up : ∫ t in (0 : ℝ)..(2 * π), (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t) ≤
      γ.c * ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hpi_pos.le hf_int hg_int
    intro t _; exact le_trans (le_abs_self _) (h_pw t)
  -- Lower bound: -(c·∫√(x²+y²)) ≤ ∫(xy'-yx')
  have h_low : -(γ.c * ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2)) ≤
      ∫ t in (0 : ℝ)..(2 * π), (γ.x t * deriv γ.y t - γ.y t * deriv γ.x t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on hpi_pos.le hg_int.neg hf_int
    intro t _; exact le_trans (neg_le_neg (h_pw t)) (neg_abs_le _)
  exact abs_le.mpr ⟨h_low, h_up⟩

-- ============================================================
-- Step 5: Arithmetic Kernel
-- ============================================================

/-- Arithmetic kernel: assembles Wirtinger bounds into 4πA ≤ L².
    This is the final step of Hurwitz's proof. Pure arithmetic.

    Inputs: L = 2πc, S = ∫√(x²+y²), Sxy = ∫(x²+y²)
    Chain: S² ≤ 2π·Sxy ≤ 2π·2πc² → S ≤ 2πc → 2A ≤ cS ≤ 2πc² → 4πA ≤ L² -/
theorem arithmetic_kernel (A L c S Sxy : ℝ)
    (hc : 0 < c) (hcirc : L = 2 * π * c) (hS_nn : 0 ≤ S)
    (harea : 2 * A ≤ c * S) (hCS : S ^ 2 ≤ 2 * π * Sxy)
    (hWirt : Sxy ≤ 2 * π * c ^ 2) :
    4 * π * A ≤ L ^ 2 := by
  have hpi : (0 : ℝ) < π := pi_pos
  have h2pic_pos : (0 : ℝ) < 2 * π * c := by positivity
  -- S² ≤ (2πc)²
  have hS2 : S ^ 2 ≤ (2 * π * c) ^ 2 :=
    calc S ^ 2 ≤ 2 * π * Sxy := hCS
         _ ≤ 2 * π * (2 * π * c ^ 2) :=
             mul_le_mul_of_nonneg_left hWirt (by linarith)
         _ = (2 * π * c) ^ 2 := by ring
  -- S ≤ 2πc
  have hS_bound : S ≤ 2 * π * c := by
    have h := Real.sqrt_le_sqrt hS2
    rwa [Real.sqrt_sq hS_nn, Real.sqrt_sq h2pic_pos.le] at h
  -- A ≤ πc² and then 4πA ≤ (2πc)² = L²
  have h1 : c * S ≤ 2 * π * c ^ 2 :=
    calc c * S ≤ c * (2 * π * c) := mul_le_mul_of_nonneg_left hS_bound (le_of_lt hc)
         _ = 2 * π * c ^ 2 := by ring
  have hA : A ≤ π * c ^ 2 := by linarith
  calc 4 * π * A ≤ 4 * π * (π * c ^ 2) :=
            mul_le_mul_of_nonneg_left hA (by linarith)
       _ = (2 * π * c) ^ 2 := by ring
       _ = L ^ 2 := by rw [hcirc]

-- ============================================================
-- THE MAIN THEOREM
-- ============================================================

/-- **Isoperimetric Inequality**: L² ≥ 4πA for nice closed curves.

    Among all smooth closed constant-speed zero-mean curves of circumference L,
    the circle encloses the maximum area. Equivalently: L² ≥ 4πA.

    **Proof** (Hurwitz 1901, via the explicit chain):
    1. **Wirtinger** on x, y: ∫(x²+y²) ≤ 2πc²    [Part II]
    2. **Integral C-S**: (∫√(x²+y²))² ≤ 2π·∫(x²+y²)   [Step 3]
    3. **Area bound**: 2A ≤ c·∫√(x²+y²)    [Step 4, from Green + 2D C-S]
    4. **Arithmetic**: chain 1-3 to get 4πA ≤ (2πc)² = L²    [Step 5]

    Depends on wirtinger_inequality (1 sorry for Parseval bridge).
    All other steps fully verified. -/
theorem isoperimetric_nice (γ : NiceCurve) :
    4 * π * γ.area ≤ γ.circumference ^ 2 := by
  rw [γ.circumference_eq]
  -- Define the auxiliary quantities
  set S := ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2)
  set Sxy := ∫ t in (0 : ℝ)..(2 * π), (γ.x t ^ 2 + γ.y t ^ 2)
  -- Verify all hypotheses for the arithmetic kernel
  have hS_nn : 0 ≤ S := by
    apply intervalIntegral.integral_nonneg (by linarith [pi_pos])
    intro t _; exact Real.sqrt_nonneg _
  have harea : 2 * γ.area ≤ γ.c * S := γ.area_bound
  have hCS : S ^ 2 ≤ 2 * π * Sxy := by
    -- Apply integral_cauchy_schwarz to f = √(x²+y²)
    set g := fun t => Real.sqrt (γ.x t ^ 2 + γ.y t ^ 2)
    have hg_cont : Continuous g := ((γ.smooth_x.continuous.pow 2).add
      (γ.smooth_y.continuous.pow 2)).sqrt
    have hg_int := hg_cont.intervalIntegrable (a := (0 : ℝ)) (b := 2 * π)
    have hg2_int := (hg_cont.pow 2).intervalIntegrable (a := (0 : ℝ)) (b := 2 * π)
    have hCS_raw := integral_cauchy_schwarz g hg_int hg2_int
    -- (√(x²+y²))² = x²+y² since the argument is non-negative
    have hg2_eq : ∀ t, g t ^ 2 = γ.x t ^ 2 + γ.y t ^ 2 :=
      fun t => Real.sq_sqrt (by positivity : (0 : ℝ) ≤ γ.x t ^ 2 + γ.y t ^ 2)
    simp_rw [hg2_eq] at hCS_raw
    exact hCS_raw
  have hWirt : Sxy ≤ 2 * π * γ.c ^ 2 := γ.wirtinger_bound
  -- Apply the arithmetic kernel
  exact arithmetic_kernel γ.area (2 * π * γ.c) γ.c S Sxy γ.c_pos rfl hS_nn harea hCS hWirt

-- ============================================================
-- Summary
-- ============================================================

/-
## Results

### Proved (0 sorries):
1. `hasDerivAt_ofReal_comp` — chain rule for ofReal ∘ f
2. `ibp_fourier` — IBP for Fourier coefficients: ĉₙ(f') = in·ĉₙ(f)
3. `norm_ibp_fourier` — norm consequence: ‖ĉₙ(f')‖ = |n|·‖ĉₙ(f)‖
4. `cross_sq_le` — 2D Cauchy-Schwarz: |xv-yu|² ≤ (x²+y²)(u²+v²)
5. `integral_cauchy_schwarz` — (∫f)² ≤ 2π·∫f² (discriminant method)
6. `NiceCurve.circumference_eq` — L = 2πc for constant-speed curves
7. `NiceCurve.wirtinger_bound` — ∫(x²+y²) ≤ 2πc² (from Wirtinger)
8. `NiceCurve.area_bound` — 2A ≤ c·∫√(x²+y²) (Green + 2D C-S)
9. `arithmetic_kernel` — pure arithmetic: Wirtinger bounds ⟹ 4πA ≤ L²
10. `isoperimetric_nice` — **the main theorem**: 4πA ≤ L²

### Sorry (1):
- `wirtinger_inequality` — Parseval bridge: converting Mathlib's
  tsum_sq_fourierCoeff (on AddCircle with Haar measure) to interval
  integrals on [0, 2π] with Lebesgue measure.

### The explicit Hurwitz chain:
  IBP (ibp_fourier) + Parseval (Mathlib) ⟹ Wirtinger (wirtinger_inequality)
  Wirtinger + Cauchy-Schwarz + Green ⟹ Isoperimetric (isoperimetric_nice)

### Connection to other files:
- The IBP formula was first proved in AreaOfCircleOQ01OQ02OQ02.lean (0 sorries)
- The Wirtinger inequality is also proved in AreaOfCircleOQ01OQ03.lean (via fourier_decomposition)
- The full isoperimetric inequality for general curves is in AreaOfCircleOQ01OQ03.lean
  (additionally needs arc-length reparametrization, sorry)
- This file contributes a clean, self-contained assembly with only 1 sorry

### To reduce to 0 sorries:
Prove the Parseval bridge: for continuous 2π-periodic f : ℝ → ℝ,
  ∫₀²π f(t)² dt = (2π) · Σₙ ‖fourierCoeffOn(ofReal ∘ f, n)‖²
This requires lifting f to AddCircle(2π), applying tsum_sq_fourierCoeff,
converting Haar → Lebesgue measure, and bridging fourierCoeff ↔ fourierCoeffOn.
See parseval_AddCircle_lift in AreaOfCircleOQ01OQ03.lean (~100 lines).
-/

end IsoperimetricAssembly
