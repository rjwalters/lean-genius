/-
  Isoperimetric Inequality: the second-derivative Fourier identity
  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-02

  The parent file `AreaOfCircleOQ01OQ02OQ02` proves the integration-by-parts
  identity for Fourier coefficients of periodic C¹ functions,

      ĉₙ(f') = i·n · ĉₙ(f).

  Iterating it once more gives the *second*-derivative identity

      ĉₙ(f'') = (i·n)² · ĉₙ(f) = −n² · ĉₙ(f),

  the `−n²` eigenvalue that drives Wirtinger's inequality and hence the
  Fourier (Hurwitz) proof of the isoperimetric inequality `C² ≥ 4πA`: each
  Fourier mode contributes a factor `n² ≥ 1`, with equality exactly on the
  first harmonic (the circle).

  This file supplies that identity, together with the supporting fact that
  the derivative of a periodic function is periodic (which Mathlib does not
  package directly).

  References:
  - Hurwitz (1901): Fourier proof of the isoperimetric inequality
  - AreaOfCircleOQ01OQ02OQ02.lean (the first-order IBP identity, reused here)
-/

import Mathlib
import Proofs.AreaOfCircleOQ01OQ02OQ02

open Real Filter Topology Complex MeasureTheory IsoperimetricFourier

noncomputable section

namespace IsoperimetricFourier

-- ============================================================
-- SECTION II: Second-derivative Fourier identity
-- ============================================================

/-- The derivative of a periodic function is periodic with the same period.
    From `f (x + T) = f x` for all `x`, the shifted function `fun x ↦ f (x + T)`
    *is* `f`, so their derivatives agree: `f' (t + T) = f' t`. -/
theorem deriv_periodic_of_periodic (f : ℝ → ℝ) (T : ℝ)
    (hperiod : ∀ t, f (t + T) = f t) (t : ℝ) :
    deriv f (t + T) = deriv f t := by
  have hshift : (fun x => f (x + T)) = f := funext hperiod
  have hstep : deriv (fun x => f (x + T)) t = deriv f (t + T) :=
    deriv_comp_add_const f T t
  rw [hshift] at hstep
  exact hstep.symm

/-- **Second-order IBP for Fourier coefficients**: for a `C²` periodic
    function `f` (period `2π`) and `n ≠ 0`,

        ĉₙ(f'') = −n² · ĉₙ(f).

    Proof: apply the first-order identity `fourierCoeffOn_deriv_periodic`
    twice — once to `f` and once to `f'` (which is again `C¹` and periodic) —
    and collapse `(i·n)·(i·n) = i²·n² = −n²` via `I_mul_I`. -/
theorem fourierCoeffOn_deriv2_periodic (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n =
      -(n : ℂ) ^ 2 * fourierCoeffOn hab (ofReal ∘ f) n := by
  -- `f` is `C¹`, and so is its derivative.
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv (n := 1)).mp hf |>.2.2
  -- The derivative inherits the periodicity of `f`.
  have hperiod' : ∀ t, deriv f (t + 2 * π) = deriv f t :=
    deriv_periodic_of_periodic f (2 * π) hperiod
  -- First-order identity applied to `f` and to `deriv f`.
  have h1 := fourierCoeffOn_deriv_periodic f hf1 hperiod hab n hn
  have h2 := fourierCoeffOn_deriv_periodic (deriv f) hdf1 hperiod' hab n hn
  rw [h2, h1]
  rw [show I * (n : ℂ) * (I * (n : ℂ) * fourierCoeffOn hab (ofReal ∘ f) n)
        = (I * I) * (n : ℂ) ^ 2 * fourierCoeffOn hab (ofReal ∘ f) n from by ring,
      I_mul_I]
  ring

/-- **The `n = 0` companion**: the derivative of a periodic function has zero
    mean, i.e. its zeroth Fourier coefficient vanishes,

        ĉ₀(f') = 0.

    Whereas `fourierCoeffOn_deriv_periodic` needs `n ≠ 0` (it divides by `n`), the
    zero mode is governed by the fundamental theorem of calculus: for a `C¹`
    periodic `f` the character `fourier 0` is constant `1`, so `ĉ₀(f')` is the
    average of `f'` over one period, and `∫₀^{2π} f' = f(2π) − f(0) = 0` by
    periodicity.  Together with the `−n²` eigenvalue for `n ≠ 0` this pins down
    the full spectrum of the differentiation operator on periodic functions:
    `0` on constants, `i·n` on the `n`-th harmonic. -/
theorem fourierCoeffOn_deriv_zero_periodic (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t) (hab : (0 : ℝ) < 2 * π) :
    fourierCoeffOn hab (ofReal ∘ deriv f) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  -- The zero character is constant `1`, so the integrand is just `f'`.
  simp only [neg_zero, fourier_zero, one_smul]
  -- `f` is differentiable and `f'` is interval-integrable (it is continuous).
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * π), DifferentiableAt ℝ f x :=
    fun x _ => hf.differentiable le_rfl x
  have hint : IntervalIntegrable (deriv f) MeasureTheory.volume 0 (2 * π) :=
    (hf.continuous_deriv le_rfl).intervalIntegrable 0 (2 * π)
  -- FTC: the integral of the derivative over a period is the boundary difference.
  have hz : ∫ x in (0 : ℝ)..(2 * π), deriv f x = f (2 * π) - f 0 :=
    intervalIntegral.integral_deriv_eq_sub hderiv hint
  -- Periodicity makes that boundary difference vanish.
  have hfp : f (2 * π) = f 0 := by have h := hperiod 0; rwa [zero_add] at h
  -- Push `ofReal` through the (real) integral, then apply the two facts above.
  have hcomp : (∫ x in (0 : ℝ)..(2 * π), (ofReal ∘ deriv f) x)
      = ((∫ x in (0 : ℝ)..(2 * π), deriv f x : ℝ) : ℂ) := by
    simp only [Function.comp]
    exact intervalIntegral.integral_ofReal
  rw [hcomp, hz, hfp, sub_self, ofReal_zero, smul_zero]

-- ============================================================
-- SECTION III: Wirtinger's inequality (Fourier / Parseval form)
-- ============================================================

/-- A continuous `ℝ → ℂ` function is `L²` on the finite-measure interval `(0, 2π]`.
    It is bounded there (continuous on the compact closure `[0, 2π]`), and the
    restricted measure is finite, so `MemLp.of_bound` applies. -/
private theorem memLp_two_of_continuous {g : ℝ → ℂ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ioc
      (fun x hx => hC x (Set.Ioc_subset_Icc_self hx)))

/-- **Wirtinger's inequality** (Fourier / Hurwitz form).  For a `C¹` function `f`
    of period `2π` whose mean over one period vanishes,

        ∫₀^{2π} f² ≤ ∫₀^{2π} (f')².

    This is the analytic heart of the Fourier proof of the isoperimetric
    inequality.  Via Parseval's identity (`hasSum_sq_fourierCoeffOn`) both sides
    are `2π` times a sum of squared Fourier coefficients:

        ∫₀^{2π} f²  = 2π · ∑ₙ |ĉₙ(f)|²,   ∫₀^{2π} (f')² = 2π · ∑ₙ |ĉₙ(f')|².

    The first-order identity `ĉₙ(f') = i·n·ĉₙ(f)` (`fourierCoeffOn_deriv_periodic`)
    gives `|ĉₙ(f')|² = n²·|ĉₙ(f)|²`, and for `n ≠ 0` the eigenvalue satisfies
    `n² ≥ 1`.  The `n = 0` mode contributes nothing on either side: `ĉ₀(f') = 0`
    (`fourierCoeffOn_deriv_zero_periodic`) and `ĉ₀(f) = 0` by the zero-mean
    hypothesis.  Hence the sums compare termwise and the inequality follows,
    with equality exactly when only the first harmonic survives — the circle. -/
theorem wirtinger_inequality (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hmean : ∫ x in (0 : ℝ)..(2 * π), f x = 0) :
    ∫ x in (0 : ℝ)..(2 * π), (f x) ^ 2 ≤ ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 := by
  have hab : (0 : ℝ) < 2 * π := by positivity
  -- Continuity of `f` and its derivative, embedded into `ℂ`.
  have hgc : Continuous (ofReal ∘ f) := Complex.continuous_ofReal.comp hf.continuous
  have hg'c : Continuous (ofReal ∘ deriv f) :=
    Complex.continuous_ofReal.comp (hf.continuous_deriv le_rfl)
  -- Parseval on `(0, 2π]` for `f` and for `f'`.
  have Pg := hasSum_sq_fourierCoeffOn hab (memLp_two_of_continuous hgc)
  have Pg' := hasSum_sq_fourierCoeffOn hab (memLp_two_of_continuous hg'c)
  -- `ĉ₀(f) = 0` (zero mean) and `ĉ₀(f') = 0` (the companion identity).
  have hc0 : fourierCoeffOn hab (ofReal ∘ f) 0 = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul]
    have hcomp : (∫ x in (0 : ℝ)..(2 * π), (ofReal ∘ f) x)
        = ((∫ x in (0 : ℝ)..(2 * π), f x : ℝ) : ℂ) := by
      simp only [Function.comp]; exact intervalIntegral.integral_ofReal
    rw [hcomp, hmean, ofReal_zero, smul_zero]
  have hc0' : fourierCoeffOn hab (ofReal ∘ deriv f) 0 = 0 :=
    fourierCoeffOn_deriv_zero_periodic f hf hperiod hab
  -- Termwise: `|ĉₙ(f)|² ≤ |ĉₙ(f')|²`.
  have key : ∀ n : ℤ,
      ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
        ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖ ^ 2 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hc0, hc0']
    · rw [fourierCoeffOn_deriv_periodic f hf hperiod hab n hn,
          norm_mul, norm_mul, Complex.norm_I, one_mul, mul_pow]
      have hn1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ ^ 2 := by
        have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
          rw [Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hn
        nlinarith [norm_nonneg ((n : ℂ))]
      exact le_mul_of_one_le_left (sq_nonneg _) hn1
  -- Compare the two Parseval sums termwise, then cancel the common `(2π)⁻¹`.
  have hle := hasSum_le key Pg Pg'
  simp only [smul_eq_mul, sub_zero] at hle
  have hfin := le_of_mul_le_mul_left hle (by positivity : (0 : ℝ) < (2 * π)⁻¹)
  -- Bridge the complex `L²` integrals back to the real squared integrals.
  have hbridge : ∀ x : ℝ, ‖(ofReal ∘ f) x‖ ^ 2 = (f x) ^ 2 := fun x => by
    simp only [Function.comp, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hbridge' : ∀ x : ℝ, ‖(ofReal ∘ deriv f) x‖ ^ 2 = (deriv f x) ^ 2 := fun x => by
    simp only [Function.comp, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hbridge, hbridge'] at hfin
  exact hfin

end IsoperimetricFourier
