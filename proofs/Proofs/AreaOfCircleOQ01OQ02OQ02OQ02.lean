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
    fun x => (hdf1.differentiable one_ne_zero).differentiableAt
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

-- ============================================================
-- SECTION III: General iterated-derivative eigenvalue
-- ============================================================

/-- **Iterated derivatives stay periodic.**  The `m`-fold derivative of a `T`-periodic
    function is again `T`-periodic, for every `m`.  Induction on `m`: the base case is the
    hypothesis, and the step is `deriv_periodic_of_periodic` applied to `deriv^[m] f`
    (using `deriv^[m+1] f = deriv (deriv^[m] f)`).  This is the periodicity input for the
    general eigenvalue identity below, subsuming both `deriv_periodic_of_periodic` (`m = 1`)
    and `deriv2_periodic_of_periodic` (`m = 2`). -/
theorem iteratedDeriv_periodic_of_periodic (f : ℝ → ℝ) (T : ℝ)
    (hperiod : ∀ t, f (t + T) = f t) :
    ∀ (m : ℕ) (t : ℝ), deriv^[m] f (t + T) = deriv^[m] f t := by
  intro m
  induction m with
  | zero => intro t; simpa using hperiod t
  | succ m ih =>
      intro t
      rw [Function.iterate_succ_apply']
      exact deriv_periodic_of_periodic (deriv^[m] f) T ih t

/-- **The full differentiation spectrum: the `(i·n)ᵐ` eigenvalue identity.**  For a `Cᵐ`
    periodic function `f` (period `2π`) and any nonzero mode `n`, the `m`-fold derivative acts
    on the `n`-th Fourier coefficient as the scalar `(i·n)ᵐ`:

        ĉₙ(f⁽ᵐ⁾) = (i·n)ᵐ · ĉₙ(f).

    This is the single structural theorem that unifies the entire derivative ladder of this
    file: `m = 1` is the parent IBP identity `fourierCoeffOn_deriv_periodic` (`i·n`), `m = 2`
    is `fourierCoeffOn_deriv2_periodic` (`(i·n)² = −n²`), and `m = 4` is
    `fourierCoeffOn_deriv4_periodic_all` (`(i·n)⁴ = n⁴`) — each a special value of the same
    eigenvalue `(i·n)ᵐ`.  Proof by induction on `m` (peeling one derivative off the *outside*,
    `f⁽ᵐ⁺¹⁾ = (f⁽ᵐ⁾)'`): the first-order identity applied to `f⁽ᵐ⁾` supplies the extra factor
    `i·n`, and the induction hypothesis supplies `(i·n)ᵐ`.  The `Cᵐ`-regularity of each
    intermediate derivative is `ContDiff.iterate_deriv'`, its periodicity
    `iteratedDeriv_periodic_of_periodic`. -/
theorem fourierCoeffOn_iteratedDeriv_periodic (m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (m : ℕ) f) (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv^[m] f) n
      = (I * (n : ℂ)) ^ m * fourierCoeffOn hab (ofReal ∘ f) n := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      -- `f⁽ᵐ⁾` is `C¹` and periodic, so the first-order identity applies to it.
      have hf' : ContDiff ℝ ((1 + m : ℕ)) f := by
        have hcast : (1 + m : ℕ) = m + 1 := by omega
        rw [hcast]; exact hf
      have hg1 : ContDiff ℝ (1 : ℕ) (deriv^[m] f) := ContDiff.iterate_deriv' 1 m hf'
      have hg1' : ContDiff ℝ 1 (deriv^[m] f) := by exact_mod_cast hg1
      have hgper : ∀ t, deriv^[m] f (t + 2 * π) = deriv^[m] f t :=
        fun t => iteratedDeriv_periodic_of_periodic f (2 * π) hperiod m t
      -- The induction hypothesis governs `f⁽ᵐ⁾` itself.
      have hfm : ContDiff ℝ (m : ℕ) f := hf.of_le (by exact_mod_cast Nat.le_succ m)
      have IH := ih f hfm hperiod
      -- `f⁽ᵐ⁺¹⁾ = (f⁽ᵐ⁾)'`; peel the outer derivative with the first-order identity.
      rw [Function.iterate_succ_apply']
      rw [fourierCoeffOn_deriv_periodic (deriv^[m] f) hg1' hgper hab n hn, IH]
      ring

/-- **Exact per-mode magnitude under the `m`-fold derivative.**  Taking norms in the eigenvalue
    identity `fourierCoeffOn_iteratedDeriv_periodic` collapses the phase `iᵐ` and leaves the
    real gain `|n|ᵐ`:

        ‖ĉₙ(f⁽ᵐ⁾)‖ = |n|ᵐ · ‖ĉₙ(f)‖.

    The uniform magnitude law behind the whole file: `m = 2` recovers
    `norm_fourierCoeffOn_deriv2_eq` (`n²`) and `m = 4` recovers `norm_fourierCoeffOn_deriv4_eq`
    (`n⁴`), since `|n|² = n²` and `|n|⁴ = n⁴`.  Each derivative multiplies a nonzero mode's
    magnitude by `|n|`, so the mean (`n = 0`) is killed for `m ≥ 1`, the first harmonic
    (`|n| = 1`) is fixed, and every higher mode grows geometrically in `m`. -/
theorem norm_fourierCoeffOn_iteratedDeriv_eq (m : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (m : ℕ) f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv^[m] f) n‖
      = |(n : ℝ)| ^ m * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [fourierCoeffOn_iteratedDeriv_periodic m f hf hperiod hab n hn, norm_mul, norm_pow]
  have hIn : ‖I * (n : ℂ)‖ = |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
  rw [hIn]

/-- **General polynomial spectral damping, `m`-th order.**  For any threshold `k ≤ |n|` the
    `m`-fold derivative inflates the `n`-th mode's magnitude by at least `kᵐ`:

        kᵐ · ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f⁽ᵐ⁾)‖.

    The order-`m` unification of the damping ladder (`sq_mul_norm_fourierCoeffOn_le_deriv2` is
    the `m = 2` case).  Immediate from the magnitude law `‖ĉₙ(f⁽ᵐ⁾)‖ = |n|ᵐ·‖ĉₙ(f)‖` together
    with `kᵐ ≤ |n|ᵐ` (from `k ≤ |n|`).  As `m → ∞` the gain `|n|ᵐ` diverges on every mode past
    the first harmonic — the spectral separation that makes the higher-order Wirtinger /
    isoperimetric estimates progressively sharper. -/
theorem pow_mul_norm_fourierCoeffOn_le_iteratedDeriv (m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (m : ℕ) f) (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (k : ℕ) (hk : k ≤ n.natAbs) :
    (k : ℝ) ^ m * ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv^[m] f) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Int.natAbs_zero, Nat.le_zero] at hk
    subst hk
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · simp [zero_pow hm.ne']
  · rw [norm_fourierCoeffOn_iteratedDeriv_eq m f hf hperiod hab n hn]
    have hkle : (k : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hk
    have hkpow : (k : ℝ) ^ m ≤ |(n : ℝ)| ^ m := by gcongr
    nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), hkpow]

/-- **Iterated-derivative kernel: `f⁽ᵐ⁾` kills mode `n` iff `f` has no mode `n` (`m ≥ 1`).**
    For any nonzero mode `n` and any order `m ≥ 1`,

        ĉₙ(f⁽ᵐ⁾) = 0  ↔  ĉₙ(f) = 0.

    The order-`m` unification of `fourierCoeffOn_deriv2_eq_zero_iff` and
    `fourierCoeffOn_deriv4_eq_zero_iff`: the `m`-fold derivative scales each nonzero mode by the
    nonzero eigenvalue `(i·n)ᵐ`, so it has the same kernel as the identity on `{n ≠ 0}`.  Hence
    the whole tower `f, f', f'', …` shares its nonzero-mode support. -/
theorem fourierCoeffOn_iteratedDeriv_eq_zero_iff (m : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (m : ℕ) f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv^[m] f) n = 0 ↔
      fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  rw [fourierCoeffOn_iteratedDeriv_periodic m f hf hperiod hab n hn, mul_eq_zero]
  have hIn : (I * (n : ℂ)) ^ m ≠ 0 :=
    pow_ne_zero m (mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hn))
  simp [hIn]

-- ============================================================
-- SECTION IV: First-order Wirtinger ladder (the classical inequality itself)
-- ============================================================

/-- **Exact first-order per-mode magnitude.**  The parent file's integration-by-parts identity
    `fourierCoeffOn_deriv_periodic` gives `ĉₙ(f') = i·n·ĉₙ(f)`; taking norms and using `‖i‖ = 1`
    yields, for a `C¹` periodic function and any nonzero mode `n`,

        ‖ĉₙ(f')‖ = |n| · ‖ĉₙ(f)‖.

    This is the *first*-order analogue of `norm_fourierCoeffOn_deriv2_eq` (`‖ĉₙ(f'')‖ = n²·‖ĉₙ(f)‖`)
    and the more fundamental one: the eigenvalue magnitude of `d/dt` on the Fourier basis is `|n|`,
    and squaring it (`|n|·|n| = n²`) recovers the second-order factor.  It is the exact per-mode form
    of Wirtinger's inequality, which the whole file is built around but which was previously stated
    only from the second derivative onward.  (The general `(i·n)ᵐ` identity of Section III gives the
    *complex* eigenvalue at every order; this is the sharpened real-magnitude / inequality reading at
    the base order, which the isoperimetric argument uses directly.) -/
theorem norm_fourierCoeffOn_deriv_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖
      = |(n : ℝ)| * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [fourierCoeffOn_deriv_periodic f hf hperiod hab n hn]
  simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]

/-- **Wirtinger's inequality, mode by mode.**  The classical first-order estimate: for a `C¹`
    periodic function and any nonzero mode `n`,

        ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f')‖,

    because the eigenvalue magnitude `|n| ≥ 1` never shrinks a nonzero mode.  Summed over `n` by
    Parseval (with the zero mode removed by the mean-zero normalization) this is exactly Wirtinger's
    inequality `∫ f² ≤ ∫ (f')²`, the analytic heart of the Hurwitz–Fourier proof of the isoperimetric
    inequality.  This is the genuine first-order statement; `norm_fourierCoeffOn_le_deriv2` is its
    second-derivative iterate. -/
theorem norm_fourierCoeffOn_le_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖ := by
  rw [norm_fourierCoeffOn_deriv_eq f hf hperiod hab n hn]
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    have hone : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast hone
  nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), h1]

/-- **Wirtinger equality on the first harmonic (first order).**  On the modes `|n| = 1` the
    magnitude identity `‖ĉₙ(f')‖ = |n|·‖ĉₙ(f)‖` degenerates to an equality of norms,

        ‖ĉₙ(f')‖ = ‖ĉₙ(f)‖   for   |n| = 1,

    because the eigenvalue factor `|n|` is exactly `1`.  This is the mode where the first-order
    Wirtinger inequality is *tight* — the first harmonic, i.e. the circle — the direct-from-`f'`
    counterpart of `norm_fourierCoeffOn_deriv2_eq_of_natAbs_one`. -/
theorem norm_fourierCoeffOn_deriv_eq_of_natAbs_one (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n.natAbs = 1) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖
      = ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have habs : |(n : ℝ)| = 1 := by
    rcases Int.natAbs_eq_iff.mp hn with h | h <;> subst h <;> norm_num
  rw [norm_fourierCoeffOn_deriv_eq f hf hperiod hab n hn0, habs, one_mul]

/-- **Strict first-order damping past the first harmonic.**  For `|n| ≥ 2` and a *nonzero* mode,

        ‖ĉₙ(f)‖ < ‖ĉₙ(f')‖,

    since the eigenvalue magnitude `|n| ≥ 2 > 1`.  Together with the `|n| = 1` equality case this
    shows the derivative strictly inflates every mode except the first harmonic — the first-order
    mechanism (one order below `norm_fourierCoeffOn_lt_deriv2_of_natAbs_ge_two`) by which the Fourier
    equality analysis forces all higher modes to vanish, leaving the circle as the unique extremal. -/
theorem norm_fourierCoeffOn_lt_deriv_of_natAbs_ge_two (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : 2 ≤ n.natAbs)
    (hne : fourierCoeffOn hab (ofReal ∘ f) n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      < ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rw [norm_fourierCoeffOn_deriv_eq f hf hperiod hab n hn0]
  have hpos : 0 < ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := norm_pos_iff.mpr hne
  have hi : (2 : ℤ) ≤ |n| := by rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hi
  nlinarith [hpos, h2]

/-- **The second-derivative factor `n²` is the first-order factor `|n|` applied twice
    (`d² = d∘d`).**  Relative to the *first* derivative, the second derivative scales a nonzero
    mode's magnitude by exactly `|n|`,

        ‖ĉₙ(f'')‖ = |n| · ‖ĉₙ(f')‖   for   n ≠ 0.

    This is `norm_fourierCoeffOn_deriv_eq` instantiated at `g = f'` (whose derivative is `f''`), so
    the composition law `n² = |n|·|n|` connecting `norm_fourierCoeffOn_deriv_eq` and
    `norm_fourierCoeffOn_deriv2_eq` becomes a machine-checked consequence of applying the first-order
    eigenvalue identity twice — the exact analogue, one order down, of
    `norm_fourierCoeffOn_deriv4_eq_sq_mul_deriv2`. -/
theorem norm_fourierCoeffOn_deriv2_eq_abs_mul_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv (deriv f)) n‖
      = |(n : ℝ)| * ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖ := by
  have hdf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv (n := 1)).mp hf |>.2.2
  have hperiod' : ∀ t, deriv f (t + 2 * π) = deriv f t :=
    deriv_periodic_of_periodic f (2 * π) hperiod
  exact norm_fourierCoeffOn_deriv_eq (deriv f) hdf1 hperiod' hab n hn

/-- **First-order kernel: `f'` kills mode `n` iff `f` has no mode `n`.**  For any nonzero mode `n`,

        ĉₙ(f') = 0  ↔  ĉₙ(f) = 0,

    immediate from `ĉₙ(f') = i·n·ĉₙ(f)` and `i·n ≠ 0`: the derivative scales each nonzero mode by
    the nonzero factor `i·n`, so it has the same kernel as the identity on `{n ≠ 0}`.  The first-order
    counterpart of `fourierCoeffOn_deriv2_eq_zero_iff` and the `m = 1` base of
    `fourierCoeffOn_iteratedDeriv_eq_zero_iff`. -/
theorem fourierCoeffOn_deriv_eq_zero_iff (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv f) n = 0 ↔
      fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  rw [fourierCoeffOn_deriv_periodic f hf hperiod hab n hn]
  have hIn : I * (n : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn)
  rw [mul_eq_zero]
  simp [hIn]

-- ============================================================
-- SECTION V: Wirtinger's inequality in INTEGRAL form (the analytic core)
-- ============================================================

/-- A continuous real function, precomposed with the coercion `ℝ → ℂ`, is `L²` on the
    finite-measure interval `(0, 2π]`.  This is exactly the square-integrability hypothesis
    that Parseval's identity `tsum_sq_fourierCoeffOn` (equivalently `hasSum_sq_fourierCoeffOn`)
    demands.  Proof: a continuous function is bounded on the compact `[0, 2π] ⊇ (0, 2π]`, and a
    bounded function on a finite measure is in every `Lᵖ`. -/
theorem memLp_two_ofReal_comp_continuous (g : ℝ → ℝ) (hg : Continuous g) :
    MemLp (ofReal ∘ g) 2 (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
      (Complex.continuous_ofReal.comp hg).continuousOn
  refine MemLp.of_bound (Complex.continuous_ofReal.comp hg).aestronglyMeasurable C ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  exact hC x (Set.Ioc_subset_Icc_self hx)

/-- **Wirtinger's inequality, integral form.**  For a `C¹` periodic function `f` with mean
    zero over one period,

        ∫₀^{2π} f²  ≤  ∫₀^{2π} (f')² .

    This is the genuine analytic heart of the Hurwitz–Fourier proof of the isoperimetric
    inequality `C² ≥ 4πA`, obtained by summing the mode-wise estimate
    `norm_fourierCoeffOn_le_deriv` (`‖ĉₙ(f)‖ ≤ ‖ĉₙ(f')‖`, `|n| ≥ 1`) against Parseval's
    identity, with the zero mode removed by the mean-zero normalization
    (`ĉ₀(f) = (2π)⁻¹∫f = 0`).  Unlike the per-mode ladder above, this is the integral
    (`∫`) statement that the geometric assembly consumes directly. -/
theorem integral_sq_le_integral_sq_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hmean : ∫ x in (0 : ℝ)..(2 * π), f x = 0) :
    ∫ x in (0 : ℝ)..(2 * π), (f x) ^ 2 ≤ ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 := by
  have hab : (0 : ℝ) < 2 * π := by positivity
  have hcontf : Continuous f := hf.continuous
  have hcontdf : Continuous (deriv f) := hf.continuous_deriv_one
  have hL2f := memLp_two_ofReal_comp_continuous f hcontf
  have hL2df := memLp_two_ofReal_comp_continuous (deriv f) hcontdf
  -- the zero mode of `f` vanishes: `ĉ₀(f) = (2π)⁻¹ ∫ f = 0`
  have hz : fourierCoeffOn hab (ofReal ∘ f) 0 = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, Function.comp_apply]
    rw [intervalIntegral.integral_ofReal, hmean, Complex.ofReal_zero, smul_zero]
  -- mode-by-mode: `‖ĉₙ(f)‖² ≤ ‖ĉₙ(f')‖²` (equality-or-larger on every mode, `0` on `n = 0`)
  have hterm : ∀ i : ℤ,
      ‖fourierCoeffOn hab (ofReal ∘ f) i‖ ^ 2
        ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv f) i‖ ^ 2 := by
    intro i
    rcases eq_or_ne i 0 with hi | hi
    · subst hi
      calc ‖fourierCoeffOn hab (ofReal ∘ f) 0‖ ^ 2
          = 0 := by rw [hz, norm_zero]; norm_num
        _ ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv f) 0‖ ^ 2 := sq_nonneg _
    · exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_fourierCoeffOn_le_deriv f hf hperiod hab i hi) 2
  -- sum both Parseval identities and compare term-by-term
  have key := hasSum_le hterm (hasSum_sq_fourierCoeffOn hab hL2f)
    (hasSum_sq_fourierCoeffOn hab hL2df)
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero,
    smul_eq_mul] at key
  -- `key : (2π)⁻¹ * ∫ f² ≤ (2π)⁻¹ * ∫ (f')²`; cancel the positive scalar
  have hpos : (0 : ℝ) < (2 * π)⁻¹ := by positivity
  exact le_of_mul_le_mul_left key hpos

end IsoperimetricFourier
