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

/-- The **second** derivative of a periodic function is periodic with the same period.
    Iterating `deriv_periodic_of_periodic`: `deriv f` is periodic (first application),
    hence so is `deriv (deriv f)` (second application).  This is the periodicity input
    that `fourierCoeffOn_deriv2_periodic` uses internally, packaged as a reusable fact. -/
theorem deriv2_periodic_of_periodic (f : ℝ → ℝ) (T : ℝ)
    (hperiod : ∀ t, f (t + T) = f t) (t : ℝ) :
    deriv (deriv f) (t + T) = deriv (deriv f) t :=
  deriv_periodic_of_periodic (deriv f) T
    (fun s => deriv_periodic_of_periodic f T hperiod s) t

/-- **Recovering `f` from `f''` on nonzero modes.**  Since `ĉₙ(f'') = −n²·ĉₙ(f)` and
    `n ≠ 0`, the `n`-th Fourier coefficient of `f` is recovered by dividing:

        ĉₙ(f) = −ĉₙ(f'') / n².

    This inverts the second-derivative operator on every nonzero Fourier mode — the
    algebraic heart of solving `f'' = g` by Fourier series (each mode `n ≠ 0` is divided
    by the eigenvalue `−n²`, while the `n = 0` mode is the obstruction/mean). -/
theorem fourierCoeffOn_eq_of_deriv2_periodic (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ f) n
      = -(fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n) / (n : ℂ) ^ 2 := by
  have hn2 : (n : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Int.cast_ne_zero.mpr hn)
  rw [fourierCoeffOn_deriv2_periodic f hf hperiod hab n hn, eq_div_iff hn2]
  ring

/-- **Per-mode Wirtinger bound.**  For a `C²` periodic function and any nonzero mode
    `n`, the eigenvalue identity `ĉₙ(f'') = −n²·ĉₙ(f)` with `n² ≥ 1` gives

        ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f'')‖,

    i.e. passing to the second derivative never shrinks a nonzero Fourier mode.  This is
    the mode-wise form of Wirtinger's inequality: summed over `n` by Parseval it yields
    `∫ f² ≤ ∫ (f'')·f` type estimates, the analytic core of the Hurwitz–Fourier proof of
    the isoperimetric inequality (`C² ≥ 4πA`), with equality forced onto the first
    harmonic `n = ±1` — the circle.  The `n = 0` mode (the mean) is the sole exception. -/
theorem norm_fourierCoeffOn_le_deriv2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖ := by
  rw [fourierCoeffOn_deriv2_periodic f hf hperiod hab n hn]
  simp only [norm_mul, norm_neg]
  have hnorm_eq : ‖(n : ℂ) ^ 2‖ = (n : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_intCast, sq_abs]
  rw [hnorm_eq]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h0 : (0 : ℤ) < n ^ 2 := by positivity
    have hge : (1 : ℤ) ≤ n ^ 2 := by omega
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((n ^ 2 : ℤ) : ℝ) := by exact_mod_cast hge
      _ = (n : ℝ) ^ 2 := by push_cast; ring
  nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), hn1]

end IsoperimetricFourier
