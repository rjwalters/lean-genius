/-
  Isoperimetric Inequality: the k-th derivative Fourier identity
  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-02-oq-01

  The grandparent `AreaOfCircleOQ01OQ02OQ02` proves the first-order
  integration-by-parts identity for Fourier coefficients of a periodic C¹
  function,

      ĉₙ(f') = i·n · ĉₙ(f),

  and the parent `AreaOfCircleOQ01OQ02OQ02OQ02` iterates it once to obtain the
  second-derivative identity `ĉₙ(f'') = −n² · ĉₙ(f)`.

  This file closes the induction, proving the identity for an *arbitrary* number
  of derivatives of a smooth (C^∞) periodic function:

      ĉₙ(f⁽ᵏ⁾) = (i·n)ᵏ · ĉₙ(f).

  This is the spectral statement underlying the entire Fourier (Hurwitz) approach
  to the isoperimetric inequality: differentiation acts diagonally on the Fourier
  basis with eigenvalue `i·n`, so the `m`-fold Laplacian-type operator `d^{2m}`
  has eigenvalue `(i·n)^{2m} = (−1)^m n^{2m}`.  The parent's `−n²` is precisely
  the `k = 2` case (recovered below as `fourierCoeffOn_deriv2_smooth`).

  The proof is a clean induction on `k`: the inductive step rewrites
  `f⁽ᵏ⁺¹⁾ = (f')⁽ᵏ⁾` (via `Function.iterate_succ_apply`), applies the induction
  hypothesis to the smooth periodic function `f'`, and peels off one more factor
  `i·n` with the first-order identity.  Smoothness (`ContDiff ℝ ∞`) is preserved
  under `deriv` (`contDiff_infty_iff_deriv`) and periodicity is preserved under
  `deriv` (`deriv_periodic_of_periodic`, from the parent), so both hypotheses
  survive each step.

  References:
  - Hurwitz (1901): Fourier proof of the isoperimetric inequality
  - AreaOfCircleOQ01OQ02OQ02OQ02.lean (the second-order identity, generalized here)
-/

import Mathlib
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ02

open Real Filter Topology Complex MeasureTheory IsoperimetricFourier
open scoped ContDiff

noncomputable section

namespace IsoperimetricFourier

-- ============================================================
-- SECTION III: k-th derivative Fourier identity
-- ============================================================

/-- **k-th-order IBP for Fourier coefficients.**  For a smooth (`C^∞`) periodic
    function `f` (period `2π`) and `n ≠ 0`,

        ĉₙ(f⁽ᵏ⁾) = (i·n)ᵏ · ĉₙ(f).

    Proved by induction on `k`.  Base `k = 0` is trivial (`f⁽⁰⁾ = f`,
    `(i·n)⁰ = 1`).  The step uses `f⁽ᵏ⁺¹⁾ = (f')⁽ᵏ⁾`, the induction hypothesis on
    the smooth periodic function `f'`, and one application of the first-order
    identity `fourierCoeffOn_deriv_periodic`. -/
theorem fourierCoeffOn_iteratedDeriv_smooth
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → (∀ t, f (t + 2 * π) = f t) →
      fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n
        = (I * (n : ℂ)) ^ k * fourierCoeffOn hab (ofReal ∘ f) n := by
  induction k with
  | zero =>
    intro f _ _
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ k ih =>
    intro f hf hper
    -- `f⁽ᵏ⁺¹⁾ = (f')⁽ᵏ⁾`.
    rw [Function.iterate_succ_apply]
    -- `f'` is again smooth and periodic.
    have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
    have hper' : ∀ t, deriv f (t + 2 * π) = deriv f t :=
      deriv_periodic_of_periodic f (2 * π) hper
    -- Induction hypothesis on `f'`, then one first-order step on `f`.
    rw [ih (deriv f) hdf hper']
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
    rw [fourierCoeffOn_deriv_periodic f hf1 hper hab n hn]
    ring

/-- User-facing form (explicit `f`): for smooth periodic `f` and `n ≠ 0`,
    `ĉₙ(f⁽ᵏ⁾) = (i·n)ᵏ · ĉₙ(f)`. -/
theorem fourierCoeffOn_iteratedDeriv
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n
      = (I * (n : ℂ)) ^ k * fourierCoeffOn hab (ofReal ∘ f) n :=
  fourierCoeffOn_iteratedDeriv_smooth hab n hn k f hf hper

/-- **Second-derivative identity recovered as the `k = 2` case.**  Since
    `(i·n)² = −n²` (via `Complex.I_sq`), the general identity specializes to the
    parent's `ĉₙ(f'') = −n² · ĉₙ(f)` — here in the smooth setting, with `f''`
    written as the two-fold iterate `deriv^[2] f`. -/
theorem fourierCoeffOn_deriv2_smooth
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv^[2] f) n
      = -(n : ℂ) ^ 2 * fourierCoeffOn hab (ofReal ∘ f) n := by
  rw [fourierCoeffOn_iteratedDeriv f hf hper hab n hn 2]
  rw [show (I * (n : ℂ)) ^ 2 = -(n : ℂ) ^ 2 from by rw [mul_pow, I_sq]; ring]

/-- **Even-order Laplacian eigenvalue.**  The `2m`-fold derivative scales the
    `n`-th Fourier mode by `(−1)ᵐ n^{2m}`: `ĉₙ(f⁽²ᵐ⁾) = (−1)ᵐ n^{2m} · ĉₙ(f)`.
    This is the diagonal action of `d^{2m}` on the Fourier basis that powers the
    higher Wirtinger / Poincaré-type inequalities. -/
theorem fourierCoeffOn_iteratedDeriv_even
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) (m : ℕ) :
    fourierCoeffOn hab (ofReal ∘ deriv^[2 * m] f) n
      = (-1 : ℂ) ^ m * (n : ℂ) ^ (2 * m) * fourierCoeffOn hab (ofReal ∘ f) n := by
  rw [fourierCoeffOn_iteratedDeriv f hf hper hab n hn (2 * m)]
  rw [show (I * (n : ℂ)) ^ (2 * m)
        = (-1 : ℂ) ^ m * (n : ℂ) ^ (2 * m) from by rw [mul_pow, pow_mul, I_sq]]

end IsoperimetricFourier
