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

/-- **General-order per-mode magnitude.**  Taking norms in the `k`-th derivative
    eigenvalue identity `ĉₙ(f⁽ᵏ⁾) = (i·n)ᵏ·ĉₙ(f)` collapses the eigenvalue to its
    modulus `‖(i·n)ᵏ‖ = |n|ᵏ` (since `‖i‖ = 1`), giving for every order `k` and every
    nonzero mode `n`,

        ‖ĉₙ(f⁽ᵏ⁾)‖ = |n|ᵏ · ‖ĉₙ(f)‖.

    This is the single magnitude law behind the parent's hand-checked special cases
    `‖ĉₙ(f'')‖ = n²·‖ĉₙ(f)‖` (`norm_fourierCoeffOn_deriv2_eq`, `k = 2`) and
    `‖ĉₙ(f'''')‖ = n⁴·‖ĉₙ(f)‖` (`norm_fourierCoeffOn_deriv4_eq`, `k = 4`) — now at *all*
    orders, even and odd alike, since the modulus `|n|ᵏ` erases the phase `(i)ᵏ` that
    distinguishes them. -/
theorem norm_fourierCoeffOn_iteratedDeriv
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖
      = |(n : ℝ)| ^ k * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [fourierCoeffOn_iteratedDeriv f hf hper hab n hn k, norm_mul, norm_pow]
  have hnorm : ‖I * (n : ℂ)‖ = |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
  rw [hnorm]

/-- **General-order mode kernel.**  For any order `k` and any nonzero mode `n`, the
    `k`-th derivative annihilates the `n`-th Fourier coefficient *exactly* when `f`
    already did:

        ĉₙ(f⁽ᵏ⁾) = 0  ↔  ĉₙ(f) = 0.

    Immediate from `ĉₙ(f⁽ᵏ⁾) = (i·n)ᵏ·ĉₙ(f)` and `(i·n)ᵏ ≠ 0`: differentiation scales
    each nonzero mode by a nonzero eigenvalue power, so `d^k` has the same kernel as the
    identity on `{n ≠ 0}`.  Generalizes the parent's `k = 2, 4` kernel lemmas
    (`fourierCoeffOn_deriv2_eq_zero_iff`, `fourierCoeffOn_deriv4_eq_zero_iff`): the whole
    derivative tower `f, f', f'', …` shares the same nonzero-mode support. -/
theorem fourierCoeffOn_iteratedDeriv_eq_zero_iff
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n = 0 ↔
      fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  rw [fourierCoeffOn_iteratedDeriv f hf hper hab n hn k, mul_eq_zero]
  have hk : (I * (n : ℂ)) ^ k ≠ 0 :=
    pow_ne_zero k (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
  simp [hk]

/-- **General-order damping: differentiation never shrinks a nonzero mode.**  Since a
    nonzero integer mode has `|n| ≥ 1`, the magnitude factor `|n|ᵏ ≥ 1`, so the general
    magnitude identity `norm_fourierCoeffOn_iteratedDeriv` yields, for every order `k` and
    every nonzero mode `n`,

        ‖ĉₙ(f)‖ ≤ ‖ĉₙ(f⁽ᵏ⁾)‖.

    The all-orders form of the parent's `norm_fourierCoeffOn_le_deriv2` (`k = 2`): each
    derivative can only *inflate* a nonzero Fourier mode (strictly, once `|n| ≥ 2`), the
    monotonicity that drives the Wirtinger/Poincaré spectral estimates. -/
theorem norm_fourierCoeffOn_le_iteratedDeriv
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖ := by
  rw [norm_fourierCoeffOn_iteratedDeriv f hf hper hab n hn k]
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have hpow : (1 : ℝ) ≤ |(n : ℝ)| ^ k := one_le_pow₀ h1
  nlinarith [norm_nonneg (fourierCoeffOn hab (ofReal ∘ f) n), hpow]

-- ============================================================
-- SECTION IV: whole-spectrum (unconditional in n) identity
-- ============================================================

/-- **Periodicity is preserved by every iterate of `deriv`.**  If `f` has period `T`, so
    does `f⁽ᵏ⁾ = deriv^[k] f`, for every order `k`.  Induction on `k`, peeling one
    derivative with `deriv_periodic_of_periodic` (the parent's first-order fact, which needs
    no differentiability hypothesis).  This is the `k`-fold generalization of
    `deriv_periodic_of_periodic` / `deriv2_periodic_of_periodic`. -/
theorem iterate_deriv_periodic (f : ℝ → ℝ) (T : ℝ)
    (hper : ∀ t, f (t + T) = f t) (k : ℕ) :
    ∀ t, deriv^[k] f (t + T) = deriv^[k] f t := by
  induction k with
  | zero => intro t; simpa using hper t
  | succ k ih =>
    intro t
    have hs : deriv^[k + 1] f = deriv (deriv^[k] f) := Function.iterate_succ_apply' deriv k f
    rw [hs]
    exact deriv_periodic_of_periodic (deriv^[k] f) T ih t

/-- **Smoothness is preserved by every iterate of `deriv`.**  For `C^∞` `f`, each derivative
    `deriv^[k] f` is again `C^∞`.  Induction on `k` via `contDiff_infty_iff_deriv` (the
    equivalence `ContDiff ℝ ∞ g ↔ Differentiable ℝ g ∧ ContDiff ℝ ∞ (deriv g)`), so the
    smoothness hypothesis of the eigenvalue identity survives each differentiation. -/
theorem contDiff_infty_iterate_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (deriv^[k] f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have hs : deriv^[k + 1] f = deriv (deriv^[k] f) := Function.iterate_succ_apply' deriv k f
    rw [hs]
    exact (contDiff_infty_iff_deriv.mp ih).2

/-- **Zero-mode annihilation at every positive order.**  For smooth periodic `f`, each
    *positive*-order derivative kills the mean (`n = 0`) Fourier coefficient:

        ĉ₀(f⁽ᵏ⁺¹⁾) = 0.

    Since `f⁽ᵏ⁺¹⁾ = (f⁽ᵏ⁾)'` and `f⁽ᵏ⁾` is `C¹` and periodic (from
    `contDiff_infty_iterate_deriv`, `iterate_deriv_periodic`), the fundamental theorem of
    calculus gives `∫₀^{2π} (f⁽ᵏ⁾)' = f⁽ᵏ⁾(2π) − f⁽ᵏ⁾(0) = 0` by periodicity, so the mean of
    `f⁽ᵏ⁺¹⁾` vanishes.  This is the all-orders generalization of the parent's
    `fourierCoeffOn_deriv2_zero` (`k = 1`): the whole derivative tower `f', f'', f''', …`
    sits in the zero-mode kernel — differentiation destroys the additive constant. -/
theorem fourierCoeffOn_iteratedDeriv_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (k : ℕ) :
    fourierCoeffOn hab (ofReal ∘ deriv^[k + 1] f) 0 = 0 := by
  have hg_smooth : ContDiff ℝ ∞ (deriv^[k] f) := contDiff_infty_iterate_deriv f hf k
  have hg_per : ∀ t, deriv^[k] f (t + 2 * π) = deriv^[k] f t :=
    iterate_deriv_periodic f (2 * π) hper k
  have hstep : (deriv^[k + 1] f) = deriv (deriv^[k] f) := Function.iterate_succ_apply' deriv k f
  rw [hstep]
  have hg1 : ContDiff ℝ 1 (deriv^[k] f) := hg_smooth.of_le (by exact_mod_cast le_top)
  have hg_diff : ∀ x, DifferentiableAt ℝ (deriv^[k] f) x :=
    fun x => (hg1.differentiable (le_refl 1)).differentiableAt
  have hcont : Continuous (deriv (deriv^[k] f)) := hg1.continuous_deriv (le_refl 1)
  have hint : IntervalIntegrable (deriv (deriv^[k] f)) volume 0 (2 * π) :=
    hcont.intervalIntegrable 0 (2 * π)
  have hreal : ∫ x in (0)..(2 * π), deriv (deriv^[k] f) x = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hg_diff x) hint]
    have h := hg_per 0
    rw [zero_add] at h
    rw [h, sub_self]
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, Function.comp_apply]
  rw [intervalIntegral.integral_ofReal, hreal]
  simp

/-- **The eigenvalue identity over the WHOLE spectrum — no `n ≠ 0` side condition.**
    Merging the nonzero-mode identity `fourierCoeffOn_iteratedDeriv` with the zero-mode
    annihilation `fourierCoeffOn_iteratedDeriv_zero`, the `k`-th derivative Fourier identity

        ĉₙ(f⁽ᵏ⁾) = (i·n)ᵏ · ĉₙ(f)

    holds for **every** `n : ℤ` and every order `k`.  At `n = 0` the eigenvalue `(i·0)ᵏ`
    degenerates: it is `1` when `k = 0` (both sides are `ĉ₀(f)`) and `0` when `k ≥ 1` (both
    sides vanish — the mean is in the kernel).  This is the clean, hypothesis-free operator
    statement — `dᵏ/dtᵏ` acts diagonally on the Fourier basis with eigenvalues `(i·n)ᵏ`
    across the entire spectrum — the all-orders analogue of the parent's
    `fourierCoeffOn_deriv2_periodic_all` (`k = 2`). -/
theorem fourierCoeffOn_iteratedDeriv_all
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (k : ℕ) :
    fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n
      = (I * (n : ℂ)) ^ k * fourierCoeffOn hab (ofReal ∘ f) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · cases k with
    | zero => simp
    | succ j =>
      rw [fourierCoeffOn_iteratedDeriv_zero f hf hper hab j]
      simp
  · exact fourierCoeffOn_iteratedDeriv f hf hper hab n hn k

/-- **General-order per-mode magnitude, over the whole spectrum.**  Taking norms in the
    unconditional identity `fourierCoeffOn_iteratedDeriv_all` gives, for **every** `n : ℤ`
    (including the mean `n = 0`) and every order `k`,

        ‖ĉₙ(f⁽ᵏ⁾)‖ = |n|ᵏ · ‖ĉₙ(f)‖.

    Drops the `n ≠ 0` hypothesis of `norm_fourierCoeffOn_iteratedDeriv`: at `n = 0` both
    sides are `0` for `k ≥ 1` (and `‖ĉ₀(f)‖` at `k = 0`), consistent with `|0|ᵏ`. -/
theorem norm_fourierCoeffOn_iteratedDeriv_all
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (k : ℕ) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖
      = |(n : ℝ)| ^ k * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [fourierCoeffOn_iteratedDeriv_all f hf hper hab n k, norm_mul, norm_pow]
  have hnorm : ‖I * (n : ℂ)‖ = |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
  rw [hnorm]

/-- **Odd-order phase.**  The `(2m+1)`-fold derivative scales the `n`-th mode by the
    *pure-imaginary* eigenvalue `(i·n)^{2m+1} = (−1)ᵐ·i·n^{2m+1}`:

        ĉₙ(f⁽²ᵐ⁺¹⁾) = (−1)ᵐ · i · n^{2m+1} · ĉₙ(f).

    The odd-order companion of `fourierCoeffOn_iteratedDeriv_even` (whose eigenvalue
    `(−1)ᵐ n^{2m}` is real): odd derivatives carry the extra factor `i`, so `d^{odd}` maps
    real cosine modes to sine modes and vice versa.  The two together fully classify the
    phase `(i)ᵏ` of the differentiation eigenvalue by the parity of `k`. -/
theorem fourierCoeffOn_iteratedDeriv_odd
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) (m : ℕ) :
    fourierCoeffOn hab (ofReal ∘ deriv^[2 * m + 1] f) n
      = (-1 : ℂ) ^ m * I * (n : ℂ) ^ (2 * m + 1) * fourierCoeffOn hab (ofReal ∘ f) n := by
  rw [fourierCoeffOn_iteratedDeriv f hf hper hab n hn (2 * m + 1)]
  rw [show (I * (n : ℂ)) ^ (2 * m + 1)
        = (-1 : ℂ) ^ m * I * (n : ℂ) ^ (2 * m + 1) from by
    rw [mul_pow, pow_succ, pow_mul, I_sq]]

end IsoperimetricFourier
