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

/-- **Exact per-mode magnitude under the second derivative.**  Sharpening
    `norm_fourierCoeffOn_le_deriv2` from an inequality to the exact identity: for a `C²`
    periodic function and any nonzero mode `n`,

        ‖ĉₙ(f'')‖ = n² · ‖ĉₙ(f)‖.

    The eigenvalue `−n²` of the second-derivative operator acts on the mode's magnitude by
    the factor `n²`.  The `≤` bound is the immediate corollary `n² ≥ 1`; here the constant
    is pinned exactly, which is what makes the Wirtinger equality analysis (below) possible. -/
theorem norm_fourierCoeffOn_deriv2_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖
      = (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [fourierCoeffOn_deriv2_periodic f hf hperiod hab n hn]
  simp only [norm_mul, norm_neg]
  have hnorm_eq : ‖(n : ℂ) ^ 2‖ = (n : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_intCast, sq_abs]
  rw [hnorm_eq]

/-- **Wirtinger equality case: the first harmonic.**  On the modes `n = ±1` the
    second-derivative magnitude identity degenerates to an equality of norms,

        ‖ĉₙ(f'')‖ = ‖ĉₙ(f)‖   for   |n| = 1,

    because the eigenvalue factor `n²` is exactly `1`.  This is the mode where Wirtinger's
    inequality is *tight* — the extremal configuration of the isoperimetric problem is the
    first harmonic, i.e. the circle.  For every higher mode `|n| ≥ 2` the factor `n² ≥ 4 > 1`
    makes the inequality strict, so equality in the Fourier (Hurwitz) proof forces all but
    the first harmonic to vanish. -/
theorem norm_fourierCoeffOn_deriv2_eq_of_natAbs_one (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n.natAbs = 1) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖
      = ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hsq : (n : ℝ) ^ 2 = 1 := by
    rcases Int.natAbs_eq_iff.mp hn with h | h <;> subst h <;> norm_num
  rw [norm_fourierCoeffOn_deriv2_eq f hf hperiod hab n hn0, hsq, one_mul]

/-- **Higher-mode strict damping (`|n| ≥ 2`).**  The other half of the Wirtinger
    dichotomy, complementing `norm_fourierCoeffOn_deriv2_eq_of_natAbs_one`: away from the
    first harmonic every Fourier mode is damped by a factor at least `4` under the second
    derivative,

        4 · ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f'')‖   for   |n| ≥ 2,

    since the eigenvalue magnitude `n² ≥ 4`.  This makes the isoperimetric inequality
    *strict* on every mode past the first harmonic, which is exactly why the Fourier
    (Hurwitz) equality analysis forces all such modes to vanish — leaving the circle
    (`|n| = 1`) as the unique extremal.  The file's magnitude identity
    `norm_fourierCoeffOn_deriv2_eq` promised this strict gap in prose; here it is a lemma. -/
theorem four_mul_norm_fourierCoeffOn_le_deriv2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : 2 ≤ n.natAbs) :
    4 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rw [norm_fourierCoeffOn_deriv2_eq f hf hperiod hab n hn0]
  have hi : (2 : ℤ) ≤ |n| := by rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hi
  have hn4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ), h2]
  nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), hn4]

/-- **The Wirtinger spectral gap, quantified exactly.**  Rearranging the magnitude identity
    `‖ĉₙ(f'')‖ = n²·‖ĉₙ(f)‖` isolates the amount by which the second derivative *grows* a
    nonzero Fourier mode,

        ‖ĉₙ(f'')‖ − ‖ĉₙ(f)‖ = (n² − 1) · ‖ĉₙ(f)‖.

    The gap factor `n² − 1` is `0` exactly on the first harmonic `|n| = 1` (Wirtinger
    equality — the circle) and strictly positive for every `|n| ≥ 2`.  This is the exact,
    signed form of the estimates `norm_fourierCoeffOn_le_deriv2` (`gap ≥ 0`) and
    `four_mul_norm_fourierCoeffOn_le_deriv2` (`gap ≥ 3·‖ĉₙ(f)‖` when `|n| ≥ 2`), which the
    file previously stated only as one-sided bounds. -/
theorem norm_fourierCoeffOn_deriv2_sub (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖
        - ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      = ((n : ℝ) ^ 2 - 1) * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [norm_fourierCoeffOn_deriv2_eq f hf hperiod hab n hn]
  ring

/-- **Strict damping past the first harmonic.**  The strict half of the Wirtinger dichotomy,
    which the docstring of `norm_fourierCoeffOn_deriv2_eq_of_natAbs_one` promised in prose:
    for `|n| ≥ 2` and a *nonzero* Fourier mode,

        ‖ĉₙ(f)‖ < ‖ĉₙ(f'')‖.

    Together with the `|n| = 1` equality case this shows the second derivative strictly
    inflates every mode except the first harmonic — the mechanism by which the Fourier
    (Hurwitz) equality analysis forces all higher modes to vanish, leaving the circle as the
    unique isoperimetric extremal.  Immediate from the factor-`4` bound and `‖ĉₙ(f)‖ > 0`. -/
theorem norm_fourierCoeffOn_lt_deriv2_of_natAbs_ge_two (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : 2 ≤ n.natAbs)
    (hne : fourierCoeffOn hab (ofReal ∘ f) n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      < ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖ := by
  have hpos : 0 < ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := norm_pos_iff.mpr hne
  have h4 := four_mul_norm_fourierCoeffOn_le_deriv2 f hf hperiod hab n hn
  linarith

/-- **Mode kernel: `f''` kills mode `n` iff `f` has no mode `n`.**  For any nonzero mode
    `n`, the second derivative annihilates the `n`-th Fourier coefficient *exactly* when `f`
    already did:

        ĉₙ(f'') = 0  ↔  ĉₙ(f) = 0.

    Immediate from the eigenvalue identity `ĉₙ(f'') = −n²·ĉₙ(f)` and `n² ≠ 0`: the
    second-derivative operator scales each nonzero mode by the nonzero factor `−n²`, so it
    has the same kernel as the identity on `{n ≠ 0}`.  This is the exact-kernel companion of
    the magnitude identity `norm_fourierCoeffOn_deriv2_eq` and the reason
    `fourierCoeffOn_eq_of_deriv2_periodic` can invert `f'' = g` mode by mode: no nonzero mode
    of `f` is lost. -/
theorem fourierCoeffOn_deriv2_eq_zero_iff (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n = 0 ↔
      fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  rw [fourierCoeffOn_deriv2_periodic f hf hperiod hab n hn]
  have hn2 : (n : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Int.cast_ne_zero.mpr hn)
  rw [mul_eq_zero]
  simp [hn2]

/-- **Spectral gap is at least `3·‖ĉₙ(f)‖` past the first harmonic.**  The exact-gap
    identity `norm_fourierCoeffOn_deriv2_sub` computes
    `‖ĉₙ(f'')‖ − ‖ĉₙ(f)‖ = (n²−1)·‖ĉₙ(f)‖`, and for `|n| ≥ 2` the factor `n²−1 ≥ 3`, so

        3·‖ĉₙ(f)‖ ≤ ‖ĉₙ(f'')‖ − ‖ĉₙ(f)‖.

    This is the explicit form of the "gap ≥ 3·‖ĉₙ(f)‖ when `|n| ≥ 2`" promised in the
    docstring of `norm_fourierCoeffOn_deriv2_sub`, quantifying the strict damping
    `norm_fourierCoeffOn_lt_deriv2_of_natAbs_ge_two` by the sharp constant `3` (the
    Wirtinger spectral gap between the first harmonic `n²−1 = 0` and the next mode). -/
theorem three_mul_norm_le_norm_fourierCoeffOn_deriv2_sub (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : 2 ≤ n.natAbs) :
    3 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖
        - ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rw [norm_fourierCoeffOn_deriv2_sub f hf hperiod hab n hn0]
  have hi : (2 : ℤ) ≤ |n| := by rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hi
  have hn4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ), h2]
  nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), hn4]

/-- **General polynomial spectral damping.**  For any natural number `m ≤ |n|`, the
second derivative damps the `n`-th Fourier mode by at least `m²`:

    m² · ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f'')‖.

This unifies the damping ladder of the file: `m = 1` recovers `norm_fourierCoeffOn_le_deriv2`
and `m = 2` recovers `four_mul_norm_fourierCoeffOn_le_deriv2`, and it captures every
threshold `m` at once (`m²` grows without bound as the mode `|n| → ∞`).  Immediate from the
magnitude identity `‖ĉₙ(f'')‖ = n²·‖ĉₙ(f)‖` together with `m² ≤ n²` (from `m ≤ |n|`). -/
theorem sq_mul_norm_fourierCoeffOn_le_deriv2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (m : ℕ) (hmn : m ≤ n.natAbs) :
    (m : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖ := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simpa using norm_nonneg (fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n)
  · have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [Int.natAbs_zero, Nat.le_zero] at hmn
      omega
    rw [norm_fourierCoeffOn_deriv2_eq f hf hperiod hab n hn0]
    have hmle : (m : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hmn
    have hmsq : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) m, hmle]
    nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), hmsq]

/-- **Zero mode: the second derivative kills the mean.**  Every theorem above requires
    `n ≠ 0`, because the eigenvalue route divides by `n`.  The remaining mode `n = 0` is
    governed instead by the Fundamental Theorem of Calculus: `ĉ₀(g)` is the period-average
    `(2π)⁻¹∫₀^{2π} g`, and for `g = f''` this integral is `f'(2π) − f'(0) = 0` by the
    periodicity of `f'` (`deriv_periodic_of_periodic`).  Hence

        ĉ₀(f'') = 0.

    This is the `n = 0` companion of the `−n²` eigenvalue identity, completing the
    differentiation spectrum: the second derivative annihilates the mean (`n = 0`) and
    scales every mode `n ≠ 0` by `−n²`.  The mean of `f` itself is the unconstrained
    kernel — the additive constant lost by differentiating. -/
theorem fourierCoeffOn_deriv2_zero (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t) (hab : (0 : ℝ) < 2 * π) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) 0 = 0 := by
  have hdf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv (n := 1)).mp hf |>.2.2
  have hdf_diff : ∀ x, DifferentiableAt ℝ (deriv f) x :=
    fun x => (hdf1.differentiable (le_refl 1)).differentiableAt
  have hcont : Continuous (deriv (deriv f)) := hdf1.continuous_deriv (le_refl 1)
  have hint : IntervalIntegrable (deriv (deriv f)) volume 0 (2 * π) :=
    hcont.intervalIntegrable 0 (2 * π)
  have hreal : ∫ x in (0)..(2 * π), deriv (deriv f) x = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hdf_diff x) hint]
    have h := deriv_periodic_of_periodic f (2 * π) hperiod 0
    rw [zero_add] at h
    rw [h, sub_self]
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, Function.comp_apply]
  rw [intervalIntegral.integral_ofReal, hreal]
  simp

/-- **The `−n²` eigenvalue identity, unconditionally over the whole spectrum.**  Merging
    `fourierCoeffOn_deriv2_periodic` (the `n ≠ 0` case) with the zero-mode annihilation
    `fourierCoeffOn_deriv2_zero`, the second-derivative Fourier identity

        ĉₙ(f'') = −n² · ĉₙ(f)

    holds for **every** `n : ℤ` — no `n ≠ 0` side condition.  The `n = 0` instance is the
    degenerate eigenvalue `0`: both sides vanish (`ĉ₀(f'') = 0` and `−0²·ĉ₀(f) = 0`), so the
    mean sits in the kernel.  This is the clean, hypothesis-free operator statement: `d²/dt²`
    acts on the Fourier basis diagonally with eigenvalues `−n²`, the whole spectrum in one
    line, driving the Wirtinger/Hurwitz isoperimetric analysis without a separate zero-mode
    carve-out. -/
theorem fourierCoeffOn_deriv2_periodic_all (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n =
      -(n : ℂ) ^ 2 * fourierCoeffOn hab (ofReal ∘ f) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [fourierCoeffOn_deriv2_zero f hf hperiod hab]; simp
  · exact fourierCoeffOn_deriv2_periodic f hf hperiod hab n hn

/-- **The `n⁴` biharmonic eigenvalue identity, over the whole spectrum.**  Iterating the
    second-derivative identity `fourierCoeffOn_deriv2_periodic_all` once more (`f''''` is
    `(f'')''`, and `f''` is again `C²` and periodic) collapses the two `−n²` factors into

        ĉₙ(f'''') = (−n²)·(−n²)·ĉₙ(f) = n⁴ · ĉₙ(f),

    for **every** `n : ℤ` (no `n ≠ 0` side condition — the mean sits in the kernel, `n⁴ = 0`
    at `n = 0`).  So the fourth-derivative (biharmonic) operator `d⁴/dt⁴` also acts
    diagonally on the Fourier basis, with the nonnegative eigenvalues `n⁴`.  This is the
    spectral input for the *higher-order* Wirtinger / clamped-plate isoperimetric estimates,
    one order beyond the `−n²` of the classical Hurwitz proof. -/
theorem fourierCoeffOn_deriv4_periodic_all (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) n =
      (n : ℂ) ^ 4 * fourierCoeffOn hab (ofReal ∘ f) n := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hdf : ContDiff ℝ 3 (deriv f) := (contDiff_succ_iff_deriv (n := 3)).mp hf |>.2.2
  have hddf : ContDiff ℝ 2 (deriv (deriv f)) :=
    (contDiff_succ_iff_deriv (n := 2)).mp hdf |>.2.2
  have hper2 : ∀ t, deriv (deriv f) (t + 2 * π) = deriv (deriv f) t :=
    deriv2_periodic_of_periodic f (2 * π) hperiod
  -- ĉₙ(f'''') = −n²·ĉₙ(f''),  then  ĉₙ(f'') = −n²·ĉₙ(f)
  have h1 := fourierCoeffOn_deriv2_periodic_all (deriv (deriv f)) hddf hper2 hab n
  have h2 := fourierCoeffOn_deriv2_periodic_all f hf2 hperiod hab n
  rw [h1, h2]
  ring

/-- **Exact per-mode magnitude under the fourth derivative.**  Taking norms in the
    biharmonic identity `fourierCoeffOn_deriv4_periodic_all` gives, for every `n : ℤ`,

        ‖ĉₙ(f'''')‖ = n⁴ · ‖ĉₙ(f)‖.

    The fourth-order analogue of `norm_fourierCoeffOn_deriv2_eq` (`‖ĉₙ(f'')‖ = n²·‖ĉₙ(f)‖`):
    the fourth derivative scales each mode's magnitude by `n⁴`, vanishing only on the mean
    `n = 0` and equal to `1` on the first harmonic `|n| = 1`, with `n⁴ ≥ 16` past it — the
    steeper spectral gap underlying higher-order Wirtinger estimates. -/
theorem norm_fourierCoeffOn_deriv4_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) n‖
      = (n : ℝ) ^ 4 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [fourierCoeffOn_deriv4_periodic_all f hf hperiod hab n, norm_mul]
  have hnorm_eq : ‖(n : ℂ) ^ 4‖ = (n : ℝ) ^ 4 := by
    rw [norm_pow, Complex.norm_intCast, ← abs_pow, abs_of_nonneg (by positivity)]
  rw [hnorm_eq]

/-- **Biharmonic Wirtinger equality on the first harmonic.**  The fourth-order analogue of
    `norm_fourierCoeffOn_deriv2_eq_of_natAbs_one`: on the modes `|n| = 1` the biharmonic
    magnitude identity `‖ĉₙ(f'''')‖ = n⁴·‖ĉₙ(f)‖` degenerates to an equality of norms,

        ‖ĉₙ(f'''')‖ = ‖ĉₙ(f)‖   for   |n| = 1,

    because the eigenvalue factor `n⁴` is exactly `1` there.  The first harmonic is the
    unique mode fixed (in magnitude) by every even derivative — the circle of the higher
    order (clamped-plate) Wirtinger analysis. -/
theorem norm_fourierCoeffOn_deriv4_eq_of_natAbs_one (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n.natAbs = 1) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) n‖
      = ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  have hsq : (n : ℝ) ^ 4 = 1 := by
    rcases Int.natAbs_eq_iff.mp hn with h | h <;> subst h <;> norm_num
  rw [norm_fourierCoeffOn_deriv4_eq f hf hperiod hab n, hsq, one_mul]

/-- **Biharmonic factor-`16` damping past the first harmonic.**  The fourth-order analogue of
    `four_mul_norm_fourierCoeffOn_le_deriv2`: away from the first harmonic every Fourier mode
    is damped by at least `16` under the fourth derivative,

        16 · ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f'''')‖   for   |n| ≥ 2,

    since the biharmonic eigenvalue magnitude `n⁴ ≥ 16`.  The steeper (`16` vs `4`) gap is why
    higher-order Wirtinger / clamped-plate estimates force all but the first harmonic to vanish
    even faster than the classical second-order Hurwitz proof. -/
theorem sixteen_mul_norm_fourierCoeffOn_le_deriv4 (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : 2 ≤ n.natAbs) :
    16 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) n‖ := by
  rw [norm_fourierCoeffOn_deriv4_eq f hf hperiod hab n]
  have hi : (2 : ℤ) ≤ |n| := by rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hi
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ), h2]
  have hn4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
    nlinarith [hn2, sq_nonneg ((n : ℝ) ^ 2 - 4)]
  nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), hn4]

/-- **Biharmonic kernel: `f''''` kills mode `n` iff `f` has no mode `n`.**  The fourth-order
    analogue of `fourierCoeffOn_deriv2_eq_zero_iff`: for any nonzero mode `n`,

        ĉₙ(f'''') = 0  ↔  ĉₙ(f) = 0,

    immediate from the biharmonic identity `ĉₙ(f'''') = n⁴·ĉₙ(f)` and `n⁴ ≠ 0` — the fourth
    derivative scales each nonzero mode by the nonzero factor `n⁴`, so it has the same kernel
    as the identity on `{n ≠ 0}`. -/
theorem fourierCoeffOn_deriv4_eq_zero_iff (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) n = 0 ↔
      fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  rw [fourierCoeffOn_deriv4_periodic_all f hf hperiod hab n]
  have hn4 : (n : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 (Int.cast_ne_zero.mpr hn)
  rw [mul_eq_zero]
  simp [hn4]

/-- **Fourth derivative kills the mean.**  The `n = 0` companion of the biharmonic suite and
    the fourth-order analogue of `fourierCoeffOn_deriv2_zero`: the biharmonic eigenvalue `n⁴`
    vanishes at `n = 0`, so

        ĉ₀(f'''') = 0.

    Immediate from the whole-spectrum identity `fourierCoeffOn_deriv4_periodic_all` at `n = 0`
    (`0⁴ = 0`): the fourth derivative annihilates the mean, just as the second derivative does. -/
theorem fourierCoeffOn_deriv4_zero (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t) (hab : (0 : ℝ) < 2 * π) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) 0 = 0 := by
  simpa using fourierCoeffOn_deriv4_periodic_all f hf hperiod hab 0

/-- **The biharmonic operator is the harmonic operator applied to `f''` (`d⁴ = d²∘d²`).**
    The fourth-derivative magnitude scales the *second*-derivative modes by exactly `n²`,

        ‖ĉₙ(f'''')‖ = n² · ‖ĉₙ(f'')‖   for   n ≠ 0.

    Where `norm_fourierCoeffOn_deriv4_eq` gives the full `n⁴` factor relative to `f`, this
    records the intermediate one-order step relative to `f''`: it is `norm_fourierCoeffOn_deriv2_eq`
    instantiated at `g = f''` (whose second derivative is `f''''`), making the composition law
    `n⁴ = n² · n²` a machine-checked consequence of applying the second-derivative eigenvalue
    identity twice rather than an independent computation. -/
theorem norm_fourierCoeffOn_deriv4_eq_sq_mul_deriv2 (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) n‖
      = (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖ := by
  have hdf : ContDiff ℝ 3 (deriv f) := (contDiff_succ_iff_deriv (n := 3)).mp hf |>.2.2
  have hddf : ContDiff ℝ 2 (deriv (deriv f)) :=
    (contDiff_succ_iff_deriv (n := 2)).mp hdf |>.2.2
  have hper2 : ∀ t, deriv (deriv f) (t + 2 * π) = deriv (deriv f) t :=
    deriv2_periodic_of_periodic f (2 * π) hperiod
  exact norm_fourierCoeffOn_deriv2_eq (deriv (deriv f)) hddf hper2 hab n hn

/-- **The biharmonic and harmonic operators share their kernel on nonzero modes.**  For any
    `n ≠ 0`,

        ĉₙ(f'''') = 0  ↔  ĉₙ(f'') = 0,

    the `d⁴ = d²∘d²` counterpart of `fourierCoeffOn_deriv4_eq_zero_iff` (which compares against
    `f`).  It is `fourierCoeffOn_deriv2_eq_zero_iff` instantiated at `g = f''`, so a mode is
    killed by the fourth derivative exactly when it is killed by the second — both scale it by a
    nonzero eigenvalue power.  Together with the direct-to-`f` version this shows the whole even
    tower `f, f'', f''''` has the same nonzero-mode support. -/
theorem fourierCoeffOn_deriv4_eq_zero_iff_deriv2 (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv (deriv (deriv (deriv f)))) n = 0 ↔
      fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n = 0 := by
  have hdf : ContDiff ℝ 3 (deriv f) := (contDiff_succ_iff_deriv (n := 3)).mp hf |>.2.2
  have hddf : ContDiff ℝ 2 (deriv (deriv f)) :=
    (contDiff_succ_iff_deriv (n := 2)).mp hdf |>.2.2
  have hper2 : ∀ t, deriv (deriv f) (t + 2 * π) = deriv (deriv f) t :=
    deriv2_periodic_of_periodic f (2 * π) hperiod
  exact fourierCoeffOn_deriv2_eq_zero_iff (deriv (deriv f)) hddf hper2 hab n hn

end IsoperimetricFourier
