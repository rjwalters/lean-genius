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

-- ============================================================
-- SECTION V: the spectral equality case of the Wirtinger damping
-- ============================================================

/-- Arithmetic helper: for `k ≥ 1`, the `k`-th power of `|n|` (as a real) equals `1`
    exactly on the unit modes `|n| = 1`. -/
private theorem abs_intCast_pow_eq_one_iff (n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    |(n : ℝ)| ^ k = 1 ↔ n.natAbs = 1 := by
  have hcast : |(n : ℝ)| = (n.natAbs : ℝ) := by
    simp
  rw [hcast]
  constructor
  · intro h
    have hnk : n.natAbs ^ k = 1 := by exact_mod_cast h
    rcases Nat.pow_eq_one.mp hnk with h1 | h1
    · exact h1
    · omega
  · intro h; rw [h]; simp

/-- Arithmetic helper: for `k ≥ 1`, the `k`-th power of `|n|` (as a real) exceeds `1`
    exactly on the higher modes `|n| ≥ 2`. -/
private theorem one_lt_abs_intCast_pow_iff (n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    1 < |(n : ℝ)| ^ k ↔ 2 ≤ n.natAbs := by
  have hcast : |(n : ℝ)| = (n.natAbs : ℝ) := by
    simp
  rw [hcast]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hle : (n.natAbs : ℝ) ≤ 1 := by
      have : n.natAbs ≤ 1 := by omega
      exact_mod_cast this
    have hpow_le : (n.natAbs : ℝ) ^ k ≤ 1 := by
      calc (n.natAbs : ℝ) ^ k ≤ 1 ^ k := by
            apply pow_le_pow_left₀ (by positivity) hle
        _ = 1 := one_pow k
    linarith
  · intro h
    have h2 : (2 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast h
    calc (1 : ℝ) < 2 := by norm_num
      _ ≤ (n.natAbs : ℝ) := h2
      _ = (n.natAbs : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n.natAbs : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk

/-- **Explicit Wirtinger deficit at a single mode.**  Subtracting the magnitude identity
    `‖ĉₙ(f⁽ᵏ⁾)‖ = |n|ᵏ·‖ĉₙ(f)‖` from `‖ĉₙ(f)‖` isolates the per-mode gain of the `k`-th
    derivative as a clean product,

        ‖ĉₙ(f⁽ᵏ⁾)‖ − ‖ĉₙ(f)‖ = (|n|ᵏ − 1)·‖ĉₙ(f)‖ ,

    valid over the whole spectrum (every `n : ℤ`, every order `k`).  The first factor
    `|n|ᵏ − 1` is `≥ 0` for `k ≥ 1` and `|n| ≥ 1`, `= 0` on the unit modes `|n| = 1`, and
    `< 0` only at the mean `n = 0` — so the sign of the deficit is read off the mode index
    alone once `f` has zero mean.  This makes transparent *why* differentiation inflates the
    energy: the surplus is supported on the `|n| ≥ 2` modes. -/
theorem norm_fourierCoeffOn_iteratedDeriv_sub
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (k : ℕ) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖
        - ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      = (|(n : ℝ)| ^ k - 1) * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
  rw [norm_fourierCoeffOn_iteratedDeriv_all f hf hper hab n k]; ring

/-- **Spectral equality case of Wirtinger (per mode).**  For a positive order `k ≥ 1`, the
    `k`-th derivative leaves the *magnitude* of the `n`-th Fourier coefficient unchanged
    exactly on the first harmonic or where the mode is already absent:

        ‖ĉₙ(f⁽ᵏ⁾)‖ = ‖ĉₙ(f)‖  ↔  (|n| = 1  ∨  ĉₙ(f) = 0).

    This is the coefficient-level statement of the equality case of Wirtinger's inequality
    `∫f² ≤ ∫(f')²`: summed by Parseval, `∫(f⁽ᵏ⁾)² = ∫f²` forces every surviving mode to have
    `|n| = 1`, i.e. `f(t) = a·cos t + b·sin t` — the *circle* in the Hurwitz proof of the
    isoperimetric inequality.  Here it is isolated at one frequency and made an iff, driven
    only by the eigenvalue magnitude `|n|ᵏ = 1 ↔ |n| = 1` for `k ≥ 1`. -/
theorem norm_fourierCoeffOn_iteratedDeriv_eq_self_iff
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖
        = ‖fourierCoeffOn hab (ofReal ∘ f) n‖
      ↔ (n.natAbs = 1 ∨ fourierCoeffOn hab (ofReal ∘ f) n = 0) := by
  rw [norm_fourierCoeffOn_iteratedDeriv_all f hf hper hab n k]
  constructor
  · intro h
    have hz : (|(n : ℝ)| ^ k - 1) * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact Or.inl ((abs_intCast_pow_eq_one_iff n k hk).mp (by linarith))
    · exact Or.inr (norm_eq_zero.mp h1)
  · rintro (h | h)
    · rw [(abs_intCast_pow_eq_one_iff n k hk).mpr h, one_mul]
    · rw [norm_eq_zero.mpr h, mul_zero]

/-- **Strict damping exactly on the higher modes.**  The companion of the equality case:
    for `k ≥ 1`, the `k`-th derivative *strictly* enlarges the `n`-th coefficient magnitude
    precisely on the modes `|n| ≥ 2` that are actually present,

        ‖ĉₙ(f)‖ < ‖ĉₙ(f⁽ᵏ⁾)‖  ↔  (|n| ≥ 2  ∧  ĉₙ(f) ≠ 0).

    Together with `norm_fourierCoeffOn_iteratedDeriv_eq_self_iff` this is a complete
    trichotomy for the damping `‖ĉₙ(f)‖ ≤ ‖ĉₙ(f⁽ᵏ⁾)‖`: strict on `|n| ≥ 2` (present modes),
    equality on `|n| ≤ 1` — the spectral origin of the strict isoperimetric deficit for every
    non-circular curve. -/
theorem norm_fourierCoeffOn_lt_iteratedDeriv_iff
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ‖fourierCoeffOn hab (ofReal ∘ f) n‖
        < ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖
      ↔ (2 ≤ n.natAbs ∧ fourierCoeffOn hab (ofReal ∘ f) n ≠ 0) := by
  rw [norm_fourierCoeffOn_iteratedDeriv_all f hf hper hab n k]
  have ha_nn : 0 ≤ ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := norm_nonneg _
  constructor
  · intro h
    have hpos : 0 < ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
      rcases eq_or_lt_of_le ha_nn with h0 | h0
      · exfalso; rw [← h0] at h; simp at h
      · exact h0
    have hne : fourierCoeffOn hab (ofReal ∘ f) n ≠ 0 := norm_pos_iff.mp hpos
    have h1lt : 1 < |(n : ℝ)| ^ k := by
      by_contra hc
      push_neg at hc
      linarith [mul_le_of_le_one_left ha_nn hc, h]
    exact ⟨(one_lt_abs_intCast_pow_iff n k hk).mp h1lt, hne⟩
  · rintro ⟨h1, h2⟩
    have hpos : 0 < ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := norm_pos_iff.mpr h2
    have h1lt : 1 < |(n : ℝ)| ^ k := (one_lt_abs_intCast_pow_iff n k hk).mpr h1
    nlinarith [hpos, h1lt]

-- ============================================================
-- SECTION VI: lifting the equality case to the Parseval sum level
--             (only the first harmonic survives — the circle)
-- ============================================================

/-- **Equality case of a termwise-dominated `HasSum` (abstract glue).**  If `a i ≤ b i`
    pointwise and both families sum to the *same* total `S`, then they agree termwise:
    `a i = b i` for every `i`.  The nonnegative slack `b − a` sums to `0`, and a
    nonnegative family with vanishing sum is zero at each index (`le_hasSum` applied to the
    difference).  This is the discrete "equality forces termwise equality" principle used to
    turn a global energy identity into per-frequency information. -/
private theorem hasSum_eq_termwise_of_le {ι : Type*} {a b : ι → ℝ} {S : ℝ}
    (hle : ∀ i, a i ≤ b i) (ha : HasSum a S) (hb : HasSum b S) (i : ι) :
    a i = b i := by
  have hd : HasSum (fun j => b j - a j) (S - S) := hb.sub ha
  rw [sub_self] at hd
  have hnn : ∀ j, 0 ≤ b j - a j := fun j => sub_nonneg.mpr (hle j)
  have hle0 : b i - a i ≤ 0 := by
    have := le_hasSum hd i (fun j _ => hnn j)
    simpa using this
  linarith [hle i]

/-- **The Parseval-sum equality case: only the first harmonic survives (the circle).**
    Fix a smooth period-`2π` function `f` with zero mean (`ĉ₀(f) = 0`) and an order `k ≥ 1`.
    Suppose the derivative `f⁽ᵏ⁾` has the *same* total spectral energy as `f`, expressed as
    the two coefficient-square families summing to a common value `S`:

        ∑ₙ ‖ĉₙ(f)‖²  =  S  =  ∑ₙ ‖ĉₙ(f⁽ᵏ⁾)‖² .

    Then **every mode other than the first harmonic is absent**:

        ∀ n, |n| ≠ 1 → ĉₙ(f) = 0 ,

    i.e. `f(t) = a·cos t + b·sin t`.  This is the coefficient form of the equality case of
    Wirtinger's inequality `∫f² ≤ ∫(f')²` (and its higher-order analogues), the spectral heart
    of the Hurwitz proof that the isoperimetric bound is attained *only* by the circle.

    Proof.  The per-mode magnitude law gives termwise domination `‖ĉₙ(f)‖² ≤ ‖ĉₙ(f⁽ᵏ⁾)‖²`
    (with `≥ 1` scaling on `n ≠ 0` and the zero-mean hypothesis covering `n = 0`).  Equal sums
    then force termwise equality of the squares (`hasSum_eq_termwise_of_le`), hence equality of
    the norms `‖ĉₙ(f⁽ᵏ⁾)‖ = ‖ĉₙ(f)‖`; the per-mode equality iff
    `norm_fourierCoeffOn_iteratedDeriv_eq_self_iff` reads off `|n| = 1 ∨ ĉₙ(f) = 0`, and the
    hypothesis `|n| ≠ 1` selects the second disjunct.

    Scope note (honesty).  The two `HasSum` hypotheses *are* the Parseval identities
    `∑ₙ ‖ĉₙ(g)‖² = (2π)⁻¹∫₀^{2π}|g|²` for `g = f, f⁽ᵏ⁾`; taking them as hypotheses isolates the
    equality-case combinatorics (the content of this file).  The remaining gap to a fully
    self-contained integral statement `∫(f⁽ᵏ⁾)² = ∫f² ⟹ f` is a first harmonic is exactly
    *discharging Parseval for `fourierCoeffOn`* (bridging to Mathlib's `tsum_sq_fourierCoeff`
    on `AddCircle`). -/
theorem fourierCoeffOn_eq_zero_of_iteratedDeriv_energy_eq
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (k : ℕ) (hk : 1 ≤ k)
    (hmean : fourierCoeffOn hab (ofReal ∘ f) 0 = 0)
    {S : ℝ}
    (hfS : HasSum (fun n : ℤ => ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2) S)
    (hdS : HasSum (fun n : ℤ => ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖ ^ 2) S) :
    ∀ n : ℤ, n.natAbs ≠ 1 → fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  -- Termwise domination of the coefficient squares.
  have hdom : ∀ n : ℤ, ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖ ^ 2 := by
    intro n
    rw [norm_fourierCoeffOn_iteratedDeriv_all f hf hper hab n k, mul_pow]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hmean]; simp
    · have h1n : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| ^ k := one_le_pow₀ h1n
      have h1sq : (1 : ℝ) ≤ (|(n : ℝ)| ^ k) ^ 2 := by nlinarith [h1]
      nlinarith [h1sq, sq_nonneg (‖fourierCoeffOn hab (ofReal ∘ f) n‖)]
  -- Equal sums ⇒ termwise equality of the squares.
  intro n hn1
  have heqsq := hasSum_eq_termwise_of_le hdom hfS hdS n
  -- Equal nonnegative squares ⇒ equal norms.
  have hnn_c : (0 : ℝ) ≤ ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := norm_nonneg _
  have hnn_d : (0 : ℝ) ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖ := norm_nonneg _
  have hnorm : ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖
      = ‖fourierCoeffOn hab (ofReal ∘ f) n‖ := by
    rw [← Real.sqrt_sq hnn_d, ← Real.sqrt_sq hnn_c, heqsq]
  -- Per-mode equality case, then discard the `|n| = 1` alternative.
  rcases (norm_fourierCoeffOn_iteratedDeriv_eq_self_iff f hf hper hab n k hk).mp hnorm with h | h
  · exact absurd h hn1
  · exact h

-- ============================================================
-- SECTION VII: discharging Parseval — the self-contained
--              integral energy statement (only the circle)
-- ============================================================

/-- **`L²` membership of the complexification of a continuous real function on `(0, 2π]`.**
    A continuous `g : ℝ → ℝ` is bounded on the compact `[0, 2π]`, so `ofReal ∘ g` is dominated
    by the constant `sSup (|g| '' [0, 2π])` (which is `L²` on the finite-measure set
    `Ioc 0 (2π)`).  This supplies the hypothesis of Mathlib's Parseval identity
    `hasSum_sq_fourierCoeffOn`, letting us turn the abstract `HasSum` hypotheses of
    `fourierCoeffOn_eq_zero_of_iteratedDeriv_energy_eq` into a genuine integral statement. -/
private theorem memLp_two_ofReal_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    MemLp (ofReal ∘ g) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  refine MeasureTheory.MemLp.mono'
    (memLp_const (sSup ((fun y => |g y|) '' Set.Icc 0 (2 * π))))
    (Complex.continuous_ofReal.comp hg).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using le_csSup
    (IsCompact.bddAbove (isCompact_Icc.image (continuous_abs.comp hg)))
    (Set.mem_image_of_mem _ (Set.Ioc_subset_Icc_self hx))

/-- `‖(ofReal x : ℂ)‖² = x²`: complexification preserves the square modulus. -/
private theorem norm_ofReal_sq (x : ℝ) : ‖(ofReal x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Parseval `HasSum` for a smooth periodic real function** (specialization of Mathlib's
    `hasSum_sq_fourierCoeffOn` to `[0, 2π]` composed with the real-square rewrite):
    the coefficient-square family of a continuous real `g` sums to `(2π)⁻¹ ∫₀^{2π} g²`. -/
private theorem hasSum_sq_fourierCoeffOn_real {g : ℝ → ℝ} (hg : Continuous g)
    (hab : (0 : ℝ) < 2 * π) :
    HasSum (fun n : ℤ => ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
      ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (g x) ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn hab (memLp_two_ofReal_of_continuous hg)
  have hint : (∫ x in (0 : ℝ)..(2 * π), ‖(ofReal ∘ g) x‖ ^ 2)
      = ∫ x in (0 : ℝ)..(2 * π), (g x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Function.comp_apply]
    exact norm_ofReal_sq (g x)
  rwa [hint] at h

/-- **Self-contained integral form of the equality case: only the first harmonic survives —
    the circle.**  Fix a smooth (`C^∞`) period-`2π` function `f` with zero mean
    (`ĉ₀(f) = 0`) and an order `k ≥ 1`.  If the `k`-th derivative has the *same*
    `L²` energy as `f`,

        ∫₀^{2π} f²  =  ∫₀^{2π} (f⁽ᵏ⁾)² ,

    then **every mode other than the first harmonic is absent**:

        ∀ n, |n| ≠ 1 → ĉₙ(f) = 0 ,

    i.e. `f(t) = a·cos t + b·sin t`.  This is the integral (Wirtinger-equality) statement of the
    Hurwitz proof that the isoperimetric bound is attained *only* by the circle — now fully
    self-contained (no `HasSum`/Parseval hypotheses), the two spectral energies having been
    discharged via Mathlib's `hasSum_sq_fourierCoeffOn`.

    Proof.  Continuity of `f` and of every iterate `f⁽ᵏ⁾` (`contDiff_infty_iterate_deriv`) feeds
    the per-function Parseval `HasSum`s (`hasSum_sq_fourierCoeffOn_real`) with totals
    `(2π)⁻¹∫f²` and `(2π)⁻¹∫(f⁽ᵏ⁾)²`; the energy identity makes those totals equal, and the
    coefficient-level equality case `fourierCoeffOn_eq_zero_of_iteratedDeriv_energy_eq` finishes. -/
theorem fourierCoeffOn_eq_zero_of_iteratedDeriv_integral_energy_eq
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (k : ℕ) (hk : 1 ≤ k)
    (hmean : fourierCoeffOn hab (ofReal ∘ f) 0 = 0)
    (henergy : (∫ x in (0 : ℝ)..(2 * π), (f x) ^ 2)
        = ∫ x in (0 : ℝ)..(2 * π), (deriv^[k] f x) ^ 2) :
    ∀ n : ℤ, n.natAbs ≠ 1 → fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  have hcont_f : Continuous f := hf.continuous
  have hcont_d : Continuous (deriv^[k] f) := (contDiff_infty_iterate_deriv f hf k).continuous
  have hfHS := hasSum_sq_fourierCoeffOn_real hcont_f hab
  have hdHS := hasSum_sq_fourierCoeffOn_real hcont_d hab
  -- The two Parseval totals coincide by the energy identity.
  have htot : ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (deriv^[k] f x) ^ 2)
      = ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (f x) ^ 2) := by
    rw [henergy]
  rw [htot] at hdHS
  exact fourierCoeffOn_eq_zero_of_iteratedDeriv_energy_eq f hf hper hab k hk hmean hfHS hdHS

-- ============================================================
-- SECTION VIII: the integral Wirtinger inequality itself
--               (∫f² ≤ ∫(f⁽ᵏ⁾)²) and its equality iff
-- ============================================================

/-- **General-order Wirtinger / Poincaré inequality (integral form).**  For a smooth
    (`C^∞`) period-`2π` function `f` with zero mean (`ĉ₀(f) = 0`) and any order `k`,

        ∫₀^{2π} f²  ≤  ∫₀^{2π} (f⁽ᵏ⁾)² .

    This is the analytic heart of the Hurwitz proof of the isoperimetric inequality: the
    energy of a zero-mean periodic function never exceeds that of any of its derivatives,
    because differentiation multiplies the `n`-th Fourier mode by `|n|ᵏ ≥ 1`.  The companion
    `fourierCoeffOn_eq_zero_of_iteratedDeriv_integral_energy_eq` shows the bound is *tight*
    only for the pure first harmonic (the circle).  (The statement is stated for every `k`;
    `k = 0` is the trivial `∫f² ≤ ∫f²`, and the interesting regime is `k ≥ 1`.)

    Proof.  Both energies are Parseval totals of the coefficient-square families
    (`hasSum_sq_fourierCoeffOn_real`), which are termwise dominated
    (`‖ĉₙ(f)‖² ≤ ‖ĉₙ(f⁽ᵏ⁾)‖²`, the `|n|ᵏ ≥ 1` scaling on `n ≠ 0` and the zero-mean
    hypothesis on `n = 0`); `hasSum_le` compares the totals and the positive Parseval
    prefactor `(2π)⁻¹` cancels. -/
theorem integral_sq_le_integral_sq_iteratedDeriv_of_mean_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (k : ℕ)
    (hmean : fourierCoeffOn hab (ofReal ∘ f) 0 = 0) :
    (∫ x in (0 : ℝ)..(2 * π), (f x) ^ 2)
      ≤ ∫ x in (0 : ℝ)..(2 * π), (deriv^[k] f x) ^ 2 := by
  have hcont_f : Continuous f := hf.continuous
  have hcont_d : Continuous (deriv^[k] f) := (contDiff_infty_iterate_deriv f hf k).continuous
  have hfHS := hasSum_sq_fourierCoeffOn_real hcont_f hab
  have hdHS := hasSum_sq_fourierCoeffOn_real hcont_d hab
  -- Termwise domination of the coefficient squares (as in the equality case).
  have hdom : ∀ n : ℤ, ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
      ≤ ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖ ^ 2 := by
    intro n
    rw [norm_fourierCoeffOn_iteratedDeriv_all f hf hper hab n k, mul_pow]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hmean]; simp
    · have h1n : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| ^ k := one_le_pow₀ h1n
      have h1sq : (1 : ℝ) ≤ (|(n : ℝ)| ^ k) ^ 2 := by nlinarith [h1]
      nlinarith [h1sq, sq_nonneg (‖fourierCoeffOn hab (ofReal ∘ f) n‖)]
  -- Compare the Parseval totals, then cancel the positive prefactor.
  have hle := hasSum_le hdom hfHS hdHS
  have hc : (0 : ℝ) < (2 * π - 0)⁻¹ := by
    have : (0 : ℝ) < 2 * π - 0 := by simpa using hab
    exact inv_pos.mpr this
  simp only [smul_eq_mul] at hle
  exact le_of_mul_le_mul_left hle hc

/-- **Reverse direction: the pure first harmonic saturates the energy.**  If `f` is smooth,
    period-`2π`, and supported on the first harmonic alone (`ĉₙ(f) = 0` for all `|n| ≠ 1`),
    then for every order `k ≥ 1` the derivative has *exactly* the same `L²` energy:

        ∫₀^{2π} f²  =  ∫₀^{2π} (f⁽ᵏ⁾)² .

    Together with the forward equality case this makes the Wirtinger bound an iff.

    Proof.  On the first harmonic `|n| = 1` the magnitude law gives `‖ĉₙ(f⁽ᵏ⁾)‖ = 1ᵏ·‖ĉₙ(f)‖`,
    and off it both sides vanish (the hypothesis kills `ĉₙ(f)`, hence `ĉₙ(f⁽ᵏ⁾) = (in)ᵏ·0`).
    So the two coefficient-square families are *equal* termwise; the Parseval sums coincide by
    `HasSum.unique`, and the positive prefactor `(2π)⁻¹` cancels. -/
theorem integral_sq_iteratedDeriv_eq_of_first_harmonic
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (k : ℕ) (hk : 1 ≤ k)
    (hfirst : ∀ n : ℤ, n.natAbs ≠ 1 → fourierCoeffOn hab (ofReal ∘ f) n = 0) :
    (∫ x in (0 : ℝ)..(2 * π), (f x) ^ 2)
      = ∫ x in (0 : ℝ)..(2 * π), (deriv^[k] f x) ^ 2 := by
  have hcont_f : Continuous f := hf.continuous
  have hcont_d : Continuous (deriv^[k] f) := (contDiff_infty_iterate_deriv f hf k).continuous
  have hfHS := hasSum_sq_fourierCoeffOn_real hcont_f hab
  have hdHS := hasSum_sq_fourierCoeffOn_real hcont_d hab
  -- Termwise *equality* of the coefficient squares.
  have hteq : ∀ n : ℤ, ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖ ^ 2
      = ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2 := by
    intro n
    rw [norm_fourierCoeffOn_iteratedDeriv_all f hf hper hab n k, mul_pow]
    rcases eq_or_ne n.natAbs 1 with h1 | h1
    · have hp : |(n : ℝ)| ^ k = 1 := (abs_intCast_pow_eq_one_iff n k hk).mpr h1
      rw [hp]; ring
    · rw [hfirst n h1]; simp
  -- Rewrite the derivative's Parseval `HasSum` onto `f`'s coefficient squares.
  have hfun : (fun n : ℤ => ‖fourierCoeffOn hab (ofReal ∘ deriv^[k] f) n‖ ^ 2)
      = (fun n : ℤ => ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2) := funext hteq
  rw [hfun] at hdHS
  have huniq := hfHS.unique hdHS
  have hc_ne : ((2 * π - 0)⁻¹ : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π - 0 := by simpa using hab
    exact ne_of_gt (inv_pos.mpr this)
  simp only [smul_eq_mul] at huniq
  exact mul_left_cancel₀ hc_ne huniq

/-- **Equality case of the general-order Wirtinger inequality (integral iff).**  For a smooth
    period-`2π` function `f` with zero mean and any order `k ≥ 1`,

        ∫₀^{2π} f²  =  ∫₀^{2π} (f⁽ᵏ⁾)²   ⟺   ∀ n, |n| ≠ 1 → ĉₙ(f) = 0 ,

    i.e. the derivative energy equals the function energy **iff** `f` is a pure first harmonic
    `f(t) = a·cos t + b·sin t`.  This packages the Hurwitz equality analysis at the integral
    level: the isoperimetric bound (in its Wirtinger form) is attained exactly by the circle.

    The forward implication is `fourierCoeffOn_eq_zero_of_iteratedDeriv_integral_energy_eq`;
    the reverse is `integral_sq_iteratedDeriv_eq_of_first_harmonic`. -/
theorem integral_sq_iteratedDeriv_eq_iff_first_harmonic
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (k : ℕ) (hk : 1 ≤ k)
    (hmean : fourierCoeffOn hab (ofReal ∘ f) 0 = 0) :
    (∫ x in (0 : ℝ)..(2 * π), (f x) ^ 2)
        = ∫ x in (0 : ℝ)..(2 * π), (deriv^[k] f x) ^ 2
      ↔ ∀ n : ℤ, n.natAbs ≠ 1 → fourierCoeffOn hab (ofReal ∘ f) n = 0 := by
  constructor
  · intro h
    exact fourierCoeffOn_eq_zero_of_iteratedDeriv_integral_energy_eq f hf hper hab k hk hmean h
  · intro h
    exact integral_sq_iteratedDeriv_eq_of_first_harmonic f hf hper hab k hk h


open ComplexConjugate

-- ============================================================
-- SECTION IX: bilinear (polarized) Parseval identity
--             — the area cross-term ∫ f·g in Fourier coordinates
-- ============================================================

/-- **Additivity of `fourierCoeffOn`** for continuous `ℂ`-valued functions on `[a, b]`.
    Mathlib supplies `fourierCoeffOn.const_smul` but no additivity lemma; continuity makes
    `fourier (-n) • F` interval-integrable, so the integral form `fourierCoeffOn_eq_integral`
    splits over the sum. -/
private theorem fourierCoeffOn_add_continuous {a b : ℝ} (hab : a < b)
    {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) (n : ℤ) :
    fourierCoeffOn hab (fun x => F x + G x) n
      = fourierCoeffOn hab F n + fourierCoeffOn hab G n := by
  have hcoe : Continuous (fun x : ℝ => (fourier (-n)) ((x : AddCircle (b - a)))) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hIF : IntervalIntegrable
      (fun x => (fourier (-n)) ((x : AddCircle (b - a))) • F x) volume a b :=
    (hcoe.smul hF).intervalIntegrable _ _
  have hIG : IntervalIntegrable
      (fun x => (fourier (-n)) ((x : AddCircle (b - a))) • G x) volume a b :=
    (hcoe.smul hG).intervalIntegrable _ _
  rw [fourierCoeffOn_eq_integral (fun x => F x + G x) n hab,
      fourierCoeffOn_eq_integral F n hab, fourierCoeffOn_eq_integral G n hab, ← smul_add]
  congr 1
  rw [← intervalIntegral.integral_add hIF hIG]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [smul_add]

/-- **Subtractivity of `fourierCoeffOn`** for continuous `ℂ`-valued functions on `[a, b]`. -/
private theorem fourierCoeffOn_sub_continuous {a b : ℝ} (hab : a < b)
    {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) (n : ℤ) :
    fourierCoeffOn hab (fun x => F x - G x) n
      = fourierCoeffOn hab F n - fourierCoeffOn hab G n := by
  have hcoe : Continuous (fun x : ℝ => (fourier (-n)) ((x : AddCircle (b - a)))) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hIF : IntervalIntegrable
      (fun x => (fourier (-n)) ((x : AddCircle (b - a))) • F x) volume a b :=
    (hcoe.smul hF).intervalIntegrable _ _
  have hIG : IntervalIntegrable
      (fun x => (fourier (-n)) ((x : AddCircle (b - a))) • G x) volume a b :=
    (hcoe.smul hG).intervalIntegrable _ _
  rw [fourierCoeffOn_eq_integral (fun x => F x - G x) n hab,
      fourierCoeffOn_eq_integral F n hab, fourierCoeffOn_eq_integral G n hab, ← smul_sub]
  congr 1
  rw [← intervalIntegral.integral_sub hIF hIG]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [smul_sub]

/-- **Polarization identity in `ℂ`:** `‖u + v‖² − ‖u − v‖² = 4·Re(u · conj v)`. -/
private theorem norm_add_sq_sub_norm_sub_sq (u v : ℂ) :
    ‖u + v‖ ^ 2 - ‖u - v‖ ^ 2 = 4 * (u * conj v).re := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Bilinear (polarized) Parseval identity on `[0, 2π]`.**  For continuous real functions
    `f, g`, the real parts of the cross products of their Fourier coefficients sum to the
    normalised `L²` inner product:

        ∑ₙ Re( ĉₙ(f) · conj ĉₙ(g) )  =  (2π)⁻¹ ∫₀^{2π} f·g .

    This is the polarization of Mathlib's diagonal Parseval `hasSum_sq_fourierCoeffOn`
    (recovered at `f = g`), obtained from the parallelogram identity
    `‖u+v‖²−‖u−v‖² = 4·Re(u·conj v)` applied to the coefficient sequences of `f ± g`.  It is
    the analytic cross-term underlying the Hurwitz–Fourier area formula `A = ∮ x dy = ∫ x·y'`,
    hence the isoperimetric inequality; Mathlib supplies only the squared-norm (`f = g`) case.

    Proof.  Apply the diagonal Parseval `HasSum` to the continuous functions `f + g` and `f − g`;
    additivity of `fourierCoeffOn` identifies their coefficients with `ĉₙ(f) ± ĉₙ(g)`.  Subtracting
    the two `HasSum`s, the termwise polarization identity collapses the summand to
    `4·Re(ĉₙ(f)·conj ĉₙ(g))`, and the integral identity
    `∫(f+g)² − ∫(f−g)² = 4∫f·g` collapses the total to `4·(2π)⁻¹∫f·g`; dividing by `4` finishes. -/
theorem hasSum_re_fourierCoeffOn_mul_conj_real
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hab : (0 : ℝ) < 2 * π) :
    HasSum (fun n : ℤ =>
        (fourierCoeffOn hab (ofReal ∘ f) n *
          conj (fourierCoeffOn hab (ofReal ∘ g) n)).re)
      ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), f x * g x) := by
  have hFc : Continuous (ofReal ∘ f) := Complex.continuous_ofReal.comp hf
  have hGc : Continuous (ofReal ∘ g) := Complex.continuous_ofReal.comp hg
  -- Diagonal Parseval for `f + g` and `f − g`.
  have H1 := hasSum_sq_fourierCoeffOn_real (g := fun x => f x + g x) (hf.add hg) hab
  have H2 := hasSum_sq_fourierCoeffOn_real (g := fun x => f x - g x) (hf.sub hg) hab
  -- Identify the coefficients of `f ± g` with `ĉₙ(f) ± ĉₙ(g)`.
  have hadd : ∀ n : ℤ, fourierCoeffOn hab (ofReal ∘ fun x => f x + g x) n
      = fourierCoeffOn hab (ofReal ∘ f) n + fourierCoeffOn hab (ofReal ∘ g) n := by
    intro n
    have he : (ofReal ∘ fun x => f x + g x)
        = (fun x => (ofReal ∘ f) x + (ofReal ∘ g) x) := by
      funext x; simp [Function.comp, Complex.ofReal_add]
    rw [he]; exact fourierCoeffOn_add_continuous hab hFc hGc n
  have hsub : ∀ n : ℤ, fourierCoeffOn hab (ofReal ∘ fun x => f x - g x) n
      = fourierCoeffOn hab (ofReal ∘ f) n - fourierCoeffOn hab (ofReal ∘ g) n := by
    intro n
    have he : (ofReal ∘ fun x => f x - g x)
        = (fun x => (ofReal ∘ f) x - (ofReal ∘ g) x) := by
      funext x; simp [Function.comp, Complex.ofReal_sub]
    rw [he]; exact fourierCoeffOn_sub_continuous hab hFc hGc n
  simp only [hadd] at H1
  simp only [hsub] at H2
  -- Interval-integrability of the (continuous) squared integrands.
  have hI1 : IntervalIntegrable (fun x => (f x + g x) ^ 2) volume 0 (2 * π) :=
    ((hf.add hg).pow 2).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun x => (f x - g x) ^ 2) volume 0 (2 * π) :=
    ((hf.sub hg).pow 2).intervalIntegrable _ _
  -- Collapse the summand via the polarization identity …
  have hfun : (fun n : ℤ =>
        (fourierCoeffOn hab (ofReal ∘ f) n *
          conj (fourierCoeffOn hab (ofReal ∘ g) n)).re)
      = fun n : ℤ => (4 : ℝ)⁻¹ *
          (‖fourierCoeffOn hab (ofReal ∘ f) n + fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2
            - ‖fourierCoeffOn hab (ofReal ∘ f) n - fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2) := by
    funext n
    rw [norm_add_sq_sub_norm_sub_sq]
    ring
  -- … and the total via `∫(f+g)² − ∫(f−g)² = 4∫f·g`.
  have htot : (2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), f x * g x
      = (4 : ℝ)⁻¹ * (((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (f x + g x) ^ 2)
          - ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (f x - g x) ^ 2)) := by
    have hpt : (∫ x in (0 : ℝ)..(2 * π), ((f x + g x) ^ 2 - (f x - g x) ^ 2))
        = ∫ x in (0 : ℝ)..(2 * π), 4 * (f x * g x) := by
      apply intervalIntegral.integral_congr; intro x _; ring
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_sub,
      ← intervalIntegral.integral_sub hI1 hI2, hpt, intervalIntegral.integral_const_mul]
    ring
  rw [hfun, htot]
  exact (H1.sub H2).mul_left (4 : ℝ)⁻¹

-- ============================================================
-- SECTION X: the Hurwitz–Fourier area formula
--            — the enclosed area ∫ f·g' in Fourier coordinates
-- ============================================================

/-- **Real-part / imaginary-part bridge for the differentiation eigenvalue.**
    For `u, v : ℂ` and `n : ℤ`,

        Re( u · conj (i·n·v) )  =  n · Im( u · conj v ).

    This is the pointwise algebra that converts the *symmetric* bilinear Parseval summand
    `Re(ĉₙ(f)·conj ĉₙ(g'))` (Section IX applied to `g'`) into the *antisymmetric* area summand
    `n·Im(ĉₙ(f)·conj ĉₙ(g))` once the derivative eigenvalue `ĉₙ(g') = i·n·ĉₙ(g)` is substituted:
    conjugation turns the factor `i·n` into `−i·n`, and `Re(−i·w) = Im(w)`. -/
private theorem re_mul_conj_I_mul (u v : ℂ) (n : ℤ) :
    (u * conj (I * (n : ℂ) * v)).re = (n : ℝ) * (u * conj v).im := by
  have hc : conj (I * (n : ℂ) * v) = -I * (n : ℂ) * conj v := by
    simp only [map_mul, Complex.conj_I, map_intCast]
  rw [hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **The Hurwitz–Fourier area formula on `[0, 2π]`.**  Let `f` be continuous and `g` smooth
    (`C^∞`) and `2π`-periodic.  Then the normalised area integral `∫ f·g'` is the antisymmetric
    Fourier bilinear form of the coefficient sequences of `f` and `g`:

        ∑ₙ n · Im( ĉₙ(f) · conj ĉₙ(g) )  =  (2π)⁻¹ ∫₀^{2π} f(t)·g'(t) dt .

    This is exactly Hurwitz's expression for the *enclosed area* of the closed curve
    `t ↦ (f(t), g(t))` — the line integral `A = ∮ f dg = ∫ f·g'` — written in Fourier
    coordinates.  Only the *cross-modes* contribute the imaginary part, weighted linearly by the
    frequency `n`; the mean mode `n = 0` drops out (its weight is `0`).  Combined with the
    diagonal Parseval `hasSum_sq_fourierCoeffOn_real` (which gives the perimeter energy
    `(2π)⁻¹∫(f'²+g'²) = ∑ n²(‖ĉₙ(f)‖²+‖ĉₙ(g)‖²)`), this is the last analytic ingredient of the
    Hurwitz isoperimetric deficit `L² − 4πA = 4π² ∑ₙ [n²(‖aₙ‖²+‖bₙ‖²) − 2n·Im(aₙ·conj bₙ)] ≥ 0`.

    Proof.  Apply the bilinear (polarized) Parseval identity `hasSum_re_fourierCoeffOn_mul_conj_real`
    to `f` and the continuous function `g' = deriv g`, giving
    `∑ₙ Re(ĉₙ(f)·conj ĉₙ(g')) = (2π)⁻¹∫ f·g'`.  The whole-spectrum eigenvalue identity
    `fourierCoeffOn_iteratedDeriv_all` (at order `k = 1`) rewrites `ĉₙ(g') = i·n·ĉₙ(g)`, and the
    pointwise bridge `re_mul_conj_I_mul` collapses each summand to `n·Im(ĉₙ(f)·conj ĉₙ(g))`. -/
theorem hasSum_fourier_area_formula
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : ContDiff ℝ ∞ g)
    (hgper : ∀ t, g (t + 2 * π) = g t) (hab : (0 : ℝ) < 2 * π) :
    HasSum (fun n : ℤ =>
        (n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n *
          conj (fourierCoeffOn hab (ofReal ∘ g) n)).im)
      ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) := by
  -- `g'` is continuous (from `g ∈ C¹`), so Section IX applies to the pair `(f, g')`.
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have hderivcont : Continuous (deriv g) := hg1.continuous_deriv (le_refl 1)
  have H := hasSum_re_fourierCoeffOn_mul_conj_real (f := f) (g := deriv g) hf hderivcont hab
  -- Derivative eigenvalue at order `k = 1`: `ĉₙ(g') = i·n·ĉₙ(g)`.
  have hcoef : ∀ n : ℤ, fourierCoeffOn hab (ofReal ∘ deriv g) n
      = I * (n : ℂ) * fourierCoeffOn hab (ofReal ∘ g) n := by
    intro n
    have h := fourierCoeffOn_iteratedDeriv_all g hg hgper hab n 1
    simpa [Function.iterate_one, pow_one] using h
  -- Collapse each Section IX summand to the antisymmetric area summand.
  have hfun : (fun n : ℤ =>
        (n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n *
          conj (fourierCoeffOn hab (ofReal ∘ g) n)).im)
      = (fun n : ℤ =>
        (fourierCoeffOn hab (ofReal ∘ f) n *
          conj (fourierCoeffOn hab (ofReal ∘ deriv g) n)).re) := by
    funext n
    rw [hcoef n, re_mul_conj_I_mul]
  rw [hfun]
  exact H

-- ============================================================
-- SECTION XI: the Hurwitz isoperimetric inequality itself
--             — the deficit ∑ₙ [n²(‖aₙ‖²+‖bₙ‖²) − 2n·Im(aₙ·conj bₙ)] ≥ 0
-- ============================================================

/-- **Perimeter energy of one coordinate in Fourier form.**  For a smooth (`C^∞`)
    period-`2π` real function `f`, the diagonal Parseval identity applied to the
    (continuous) derivative `f'`, combined with the derivative eigenvalue
    `ĉₙ(f') = i·n·ĉₙ(f)`, gives the frequency-weighted energy identity

        ∑ₙ n²·‖ĉₙ(f)‖²  =  (2π)⁻¹ ∫₀^{2π} (f'(t))² dt .

    This is one coordinate's contribution to the perimeter term `(2π)⁻¹∫(f'²+g'²)` of the
    Hurwitz isoperimetric deficit.

    Proof.  Apply `hasSum_sq_fourierCoeffOn_real` to the continuous function `f'`; the
    whole-spectrum magnitude law `norm_fourierCoeffOn_iteratedDeriv_all` (at order `k = 1`)
    rewrites `‖ĉₙ(f')‖² = |n|²·‖ĉₙ(f)‖² = n²·‖ĉₙ(f)‖²`. -/
private theorem hasSum_nsq_normSq_fourierCoeffOn
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hper : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) :
    HasSum (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2)
      ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2) := by
  have hdc : Continuous (deriv f) := by
    have h := (contDiff_infty_iterate_deriv f hf 1).continuous
    rwa [Function.iterate_one] at h
  have HS := hasSum_sq_fourierCoeffOn_real hdc hab
  have hkey : (fun n : ℤ => ‖fourierCoeffOn hab (ofReal ∘ deriv f) n‖ ^ 2)
      = (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2) := by
    funext n
    have h := norm_fourierCoeffOn_iteratedDeriv_all f hf hper hab n 1
    rw [Function.iterate_one] at h
    rw [h, mul_pow, pow_one, sq_abs]
  rwa [hkey] at HS

/-- **Per-mode nonnegativity of the isoperimetric deficit.**  For any `a b : ℂ` and `n : ℤ`,

        0  ≤  n²·‖a‖² + n²·‖b‖² − 2n·Im(a·conj b) .

    This is the frequency-`n` summand of the Hurwitz deficit `L² − 4πA`.  It is the pointwise
    inequality `2n·Im(a·conj b) ≤ |n|(‖a‖²+‖b‖²) ≤ n²(‖a‖²+‖b‖²)`, built from
    `|Im(a·conj b)| ≤ ‖a‖‖b‖` (Cauchy–Schwarz in ℂ) and the integer fact `|n| ≤ n²`.
    Rewritten, the summand dominates `n²(‖a‖−‖b‖)² ≥ 0`; it vanishes exactly on the unit
    modes with `‖a‖ = ‖b‖` and `a·conj b` purely imaginary — the spectral signature of the
    circle. -/
private theorem area_deficit_summand_nonneg (a b : ℂ) (n : ℤ) :
    0 ≤ (n : ℝ) ^ 2 * ‖a‖ ^ 2 + (n : ℝ) ^ 2 * ‖b‖ ^ 2
        - 2 * (n : ℝ) * (a * conj b).im := by
  have himabs : |(a * conj b).im| ≤ ‖a‖ * ‖b‖ := by
    have h := Complex.abs_im_le_norm (a * conj b)
    rwa [norm_mul, Complex.norm_conj] at h
  have hNsq : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      nlinarith [h1, sq_abs (n : ℝ), abs_nonneg (n : ℝ)]
  have hNw : (n : ℝ) * (a * conj b).im ≤ (n : ℝ) ^ 2 * (‖a‖ * ‖b‖) :=
    calc (n : ℝ) * (a * conj b).im
        ≤ |(n : ℝ) * (a * conj b).im| := le_abs_self _
      _ = |(n : ℝ)| * |(a * conj b).im| := abs_mul _ _
      _ ≤ |(n : ℝ)| * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_left himabs (abs_nonneg _)
      _ ≤ (n : ℝ) ^ 2 * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_right hNsq (by positivity)
  nlinarith [hNw, mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg (‖a‖ - ‖b‖))]

/-- **The Hurwitz isoperimetric inequality — analytic (Wirtinger) form.**  For smooth (`C^∞`)
    period-`2π` real functions `f, g` — the coordinates of a closed plane curve
    `t ↦ (f(t), g(t))` —

        2 ∫₀^{2π} f·g'  ≤  ∫₀^{2π} ((f')² + (g')²) ,

    the two sides being `4π·A/(2π)` and the perimeter energy.  The nonnegative difference is
    `∑ₙ [n²(‖ĉₙf‖²+‖ĉₙg‖²) − 2n·Im(ĉₙf·conj ĉₙg)]`, the Hurwitz spectral deficit.

    Proof.  The perimeter energy `(2π)⁻¹∫(f'²+g'²)` is `∑ n²(‖aₙ‖²+‖bₙ‖²)`
    (`hasSum_nsq_normSq_fourierCoeffOn`, once per coordinate), and the area `(2π)⁻¹∫f·g'` is
    `∑ n·Im(aₙ·conj bₙ)` (`hasSum_fourier_area_formula`).  Subtracting `2×` the area `HasSum`
    from the perimeter `HasSum` gives a series whose every term is `≥ 0`
    (`area_deficit_summand_nonneg`), so its total `(2π)⁻¹[∫(f'²+g'²) − 2∫f·g'] ≥ 0`; clearing
    the positive factor `(2π)⁻¹` and recombining the two perimeter integrals finishes. -/
theorem two_mul_integral_mul_deriv_le_integral_add_sq_deriv
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) :
    2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x
      ≤ ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2) := by
  -- Perimeter energy of each coordinate, and the area cross term.
  have HSf := hasSum_nsq_normSq_fourierCoeffOn hf hfper hab
  have HSg := hasSum_nsq_normSq_fourierCoeffOn hg hgper hab
  have HSA := hasSum_fourier_area_formula hf.continuous hg hgper hab
  -- Deficit = perimeter − 2·area, as a `HasSum` with nonnegative terms.
  have HSdef := (HSf.add HSg).sub (HSA.mul_left 2)
  have htot_nonneg :
      (0 : ℝ) ≤ ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2)
          + ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), (deriv g x) ^ 2)
          - 2 * ((2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) :=
    HSdef.nonneg (fun n => by
      convert area_deficit_summand_nonneg
        (fourierCoeffOn hab (ofReal ∘ f) n) (fourierCoeffOn hab (ofReal ∘ g) n) n using 1
      ring)
  -- Clear the positive `(2π)⁻¹` scaling.
  simp only [smul_eq_mul, sub_zero] at htot_nonneg
  set If := ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 with hIf
  set Ig := ∫ x in (0 : ℝ)..(2 * π), (deriv g x) ^ 2 with hIg
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have hc : (0 : ℝ) < (2 * π)⁻¹ := inv_pos.mpr hab
  have hZ : (2 * π)⁻¹ * If + (2 * π)⁻¹ * Ig - 2 * ((2 * π)⁻¹ * IA)
      = (2 * π)⁻¹ * (If + Ig - 2 * IA) := by ring
  rw [hZ] at htot_nonneg
  have hZnn : 0 ≤ If + Ig - 2 * IA := by nlinarith [htot_nonneg, hc]
  -- Recombine the two perimeter integrals.
  have hdfc : Continuous (deriv f) := by
    have h := (contDiff_infty_iterate_deriv f hf 1).continuous
    rwa [Function.iterate_one] at h
  have hdgc : Continuous (deriv g) := by
    have h := (contDiff_infty_iterate_deriv g hg 1).continuous
    rwa [Function.iterate_one] at h
  have hsplit : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = If + Ig := by
    rw [hIf, hIg]
    exact intervalIntegral.integral_add
      ((hdfc.pow 2).intervalIntegrable _ _) ((hdgc.pow 2).intervalIntegrable _ _)
  rw [hsplit]
  linarith [hZnn]

/-- **The classical isoperimetric inequality `4πA ≤ L²` (Hurwitz).**  Let `f, g` be smooth
    period-`2π` coordinates of a closed plane curve parametrized with *constant speed*
    `(f'(t))² + (g'(t))² = c`.  Then the perimeter energy is `∫(f'²+g'²) = 2π·c`, so the
    squared perimeter is `L² = (2π√c)² = (2π)²·c`, and the enclosed area
    `A = ∮ f dg = ∫₀^{2π} f·g'` obeys

        4π·A  ≤  (2π)²·c  =  L² ,

    with equality iff the curve is a circle.  This is the classical isoperimetric inequality,
    read off from the analytic Wirtinger form `2∫f·g' ≤ ∫(f'²+g'²)` by evaluating the
    constant-speed perimeter energy.  (The constant-speed hypothesis is what makes
    `2π·∫(f'²+g'²)` equal to the true squared perimeter `(∮√(f'²+g'²))²`; in general the
    former dominates the latter by Cauchy–Schwarz, so the stated inequality is the sharp one.) -/
theorem isoperimetric_inequality_of_constant_speed
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c) :
    4 * π * (∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) ≤ (2 * π) ^ 2 * c := by
  have hmain := two_mul_integral_mul_deriv_le_integral_add_sq_deriv hf hg hfper hgper hab
  have hperim : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = (2 * π) * c := by
    have hEq : Set.EqOn (fun x => (deriv f x) ^ 2 + (deriv g x) ^ 2) (fun _ => c)
        (Set.uIcc 0 (2 * π)) := fun x _ => hspeed x
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_const]
    simp
  have h2 : 2 * (∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) ≤ 2 * π * c := by
    rw [← hperim]; exact hmain
  nlinarith [h2, le_of_lt hab]

-- ============================================================
-- SECTION XII: the equality case — saturation forces the circle
--   (only the 0th and 1st harmonics survive; higher modes vanish)
-- ============================================================

/-- **Sharpened per-mode deficit bound.**  For any `a b : ℂ` and `n : ℤ`, the frequency-`n`
    Hurwitz deficit summand dominates `(|n|² − |n|)·(‖a‖² + ‖b‖²)`:

        (|n|² − |n|)·(‖a‖² + ‖b‖²)  ≤  n²‖a‖² + n²‖b‖² − 2n·Im(a·conj b) .

    The gap is `|n|·(‖a‖ − ‖b‖)² ≥ 0`.  On `|n| ≥ 2` the coefficient `|n|² − |n| ≥ 2` is
    strictly positive, so a *vanishing* summand forces `‖a‖² + ‖b‖² = 0` — the mechanism by
    which equality in the isoperimetric inequality kills every harmonic above the first. -/
private theorem area_deficit_summand_ge_gap (a b : ℂ) (n : ℤ) :
    (|(n : ℝ)| ^ 2 - |(n : ℝ)|) * (‖a‖ ^ 2 + ‖b‖ ^ 2)
      ≤ (n : ℝ) ^ 2 * ‖a‖ ^ 2 + (n : ℝ) ^ 2 * ‖b‖ ^ 2 - 2 * (n : ℝ) * (a * conj b).im := by
  have himabs : |(a * conj b).im| ≤ ‖a‖ * ‖b‖ := by
    have h := Complex.abs_im_le_norm (a * conj b)
    rwa [norm_mul, Complex.norm_conj] at h
  have hbound : (n : ℝ) * (a * conj b).im ≤ |(n : ℝ)| * (‖a‖ * ‖b‖) :=
    calc (n : ℝ) * (a * conj b).im
        ≤ |(n : ℝ) * (a * conj b).im| := le_abs_self _
      _ = |(n : ℝ)| * |(a * conj b).im| := abs_mul _ _
      _ ≤ |(n : ℝ)| * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_left himabs (abs_nonneg _)
  have hsq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  nlinarith [hbound, hsq, mul_nonneg (abs_nonneg (n : ℝ)) (sq_nonneg (‖a‖ - ‖b‖))]

/-- **A vanishing high-frequency deficit summand annihilates the mode.**  If `|n| ≥ 2` and the
    frequency-`n` Hurwitz deficit summand is zero, then both Fourier amplitudes vanish:
    `a = 0` and `b = 0`.  (`|n| ≥ 2` gives `|n|² − |n| ≥ 2 > 0`, and the sharpened bound
    `area_deficit_summand_ge_gap` then forces `‖a‖² + ‖b‖² = 0`.) -/
private theorem fourierAmp_eq_zero_of_deficit_zero (a b : ℂ) (n : ℤ) (hn : 2 ≤ n.natAbs)
    (hzero : (n : ℝ) ^ 2 * ‖a‖ ^ 2 + (n : ℝ) ^ 2 * ‖b‖ ^ 2 - 2 * (n : ℝ) * (a * conj b).im = 0) :
    a = 0 ∧ b = 0 := by
  have hge := area_deficit_summand_ge_gap a b n
  rw [hzero] at hge
  -- `hge : (|n|² − |n|)·(‖a‖² + ‖b‖²) ≤ 0`
  have hm : (2 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (show (2 : ℤ) ≤ |n| by rw [Int.abs_eq_natAbs]; exact_mod_cast hn)
  have hP : (0 : ℝ) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by positivity
  have hcoef : (2 : ℝ) ≤ |(n : ℝ)| ^ 2 - |(n : ℝ)| := by
    nlinarith [hm, mul_nonneg (by linarith [hm] : (0 : ℝ) ≤ |(n : ℝ)| - 2)
      (by linarith [hm] : (0 : ℝ) ≤ |(n : ℝ)| + 1)]
  have hPzero : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ 0 := by
    nlinarith [hge, hcoef, hP,
      mul_nonneg (by linarith [hcoef] : (0 : ℝ) ≤ |(n : ℝ)| ^ 2 - |(n : ℝ)| - 2) hP]
  have ha2 : ‖a‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖b‖, hPzero]) (sq_nonneg _)
  have hb2 : ‖b‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖a‖, hPzero]) (sq_nonneg _)
  refine ⟨norm_eq_zero.mp ?_, norm_eq_zero.mp ?_⟩
  · exact (pow_eq_zero_iff (by norm_num)).mp ha2
  · exact (pow_eq_zero_iff (by norm_num)).mp hb2

/-- **Equality case of the Hurwitz isoperimetric inequality — spectral rigidity.**  For smooth
    (`C^∞`) period-`2π` real coordinates `f, g`, suppose the analytic Wirtinger inequality is
    *saturated*:

        2 ∫₀^{2π} f·g'  =  ∫₀^{2π} ((f')² + (g')²) .

    Then **every Fourier mode above the first vanishes**:

        ∀ n, |n| ≥ 2 → ĉₙ(f) = 0 ∧ ĉₙ(g) = 0 ,

    so `f` and `g` are trigonometric polynomials of degree `≤ 1` — the curve `t ↦ (f,g)` is an
    ellipse, and (with the constant-speed hypothesis, cf. `fourierCoeff_eq_zero_of_isoperimetric_saturation`)
    a circle.  This is the forward direction of Hurwitz's "equality iff the circle".

    Proof.  The Hurwitz deficit is a `HasSum` of the per-mode terms
    `n²(‖ĉₙf‖² + ‖ĉₙg‖²) − 2n·Im(ĉₙf·conj ĉₙg)`, each `≥ 0` (`area_deficit_summand_nonneg`),
    whose total `(2π)⁻¹[∫(f'²+g'²) − 2∫f·g']` is `0` under saturation.  A nonnegative summable
    family with vanishing total is termwise zero (`le_hasSum`), and on `|n| ≥ 2` a zero summand
    kills the mode (`fourierAmp_eq_zero_of_deficit_zero`). -/
theorem fourierCoeff_eq_zero_of_wirtinger_saturation
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π)
    (hEq : 2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x
            = ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) :
    ∀ n : ℤ, 2 ≤ n.natAbs →
      fourierCoeffOn hab (ofReal ∘ f) n = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) n = 0 := by
  -- Continuity of the two derivatives (for the integral split).
  have hdfc : Continuous (deriv f) := by
    have h := (contDiff_infty_iterate_deriv f hf 1).continuous
    rwa [Function.iterate_one] at h
  have hdgc : Continuous (deriv g) := by
    have h := (contDiff_infty_iterate_deriv g hg 1).continuous
    rwa [Function.iterate_one] at h
  -- The three Fourier `HasSum`s and the deficit series.
  have HSf := hasSum_nsq_normSq_fourierCoeffOn hf hfper hab
  have HSg := hasSum_nsq_normSq_fourierCoeffOn hg hgper hab
  have HSA := hasSum_fourier_area_formula hf.continuous hg hgper hab
  set If := ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 with hIf
  set Ig := ∫ x in (0 : ℝ)..(2 * π), (deriv g x) ^ 2 with hIg
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have HSdef := (HSf.add HSg).sub (HSA.mul_left 2)
  -- The total deficit is zero under saturation.
  have hsplit : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = If + Ig := by
    rw [hIf, hIg]
    exact intervalIntegral.integral_add
      ((hdfc.pow 2).intervalIntegrable _ _) ((hdgc.pow 2).intervalIntegrable _ _)
  have hTzero : ((2 * π - 0)⁻¹ • If) + ((2 * π - 0)⁻¹ • Ig)
      - 2 * ((2 * π - 0)⁻¹ • IA) = 0 := by
    simp only [smul_eq_mul, sub_zero]
    rw [hsplit] at hEq
    have hfac : (2 * π)⁻¹ * If + (2 * π)⁻¹ * Ig - 2 * ((2 * π)⁻¹ * IA)
        = (2 * π)⁻¹ * (If + Ig - 2 * IA) := by ring
    rw [hfac, show If + Ig - 2 * IA = 0 from by linarith, mul_zero]
  rw [hTzero] at HSdef
  -- Termwise: each deficit summand is zero, so high modes vanish.
  intro n hn
  have hle := le_hasSum HSdef n (fun m _ => by
    convert area_deficit_summand_nonneg (fourierCoeffOn hab (ofReal ∘ f) m)
      (fourierCoeffOn hab (ofReal ∘ g) m) m using 1; ring)
  have hge := area_deficit_summand_nonneg (fourierCoeffOn hab (ofReal ∘ f) n)
    (fourierCoeffOn hab (ofReal ∘ g) n) n
  exact fourierAmp_eq_zero_of_deficit_zero (fourierCoeffOn hab (ofReal ∘ f) n)
    (fourierCoeffOn hab (ofReal ∘ g) n) n hn (le_antisymm (by nlinarith [hle]) hge)

/-- **Geometric equality case: isoperimetric saturation forces the circle.**  Let `f, g` be
    smooth period-`2π` coordinates parametrized with *constant speed* `(f')² + (g')² = c`.  If
    the isoperimetric bound `4π·A ≤ L² = (2π)²·c` is *attained*,

        4π · (∫₀^{2π} f·g')  =  (2π)² · c ,

    then every Fourier mode above the first vanishes: `∀ n, |n| ≥ 2 → ĉₙ(f) = ĉₙ(g) = 0`.
    Together with constant speed this pins the curve to a genuine circle — the sharpness half of
    `isoperimetric_inequality_of_constant_speed`.

    Proof.  Constant speed gives `∫(f'²+g'²) = 2π·c`, and saturation gives `∫f·g' = π·c`, so
    `2∫f·g' = 2π·c = ∫(f'²+g'²)`: the analytic Wirtinger inequality is saturated and
    `fourierCoeff_eq_zero_of_wirtinger_saturation` applies. -/
theorem fourierCoeff_eq_zero_of_isoperimetric_saturation
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c)
    (hsat : 4 * π * (∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) = (2 * π) ^ 2 * c) :
    ∀ n : ℤ, 2 ≤ n.natAbs →
      fourierCoeffOn hab (ofReal ∘ f) n = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) n = 0 := by
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  -- Constant-speed perimeter energy.
  have hperim : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = (2 * π) * c := by
    have hEqOn : Set.EqOn (fun x => (deriv f x) ^ 2 + (deriv g x) ^ 2) (fun _ => c)
        (Set.uIcc 0 (2 * π)) := fun x _ => hspeed x
    rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_const]
    simp
  -- Saturation pins `IA = π·c`, hence the analytic Wirtinger equality.
  have hIAval : IA = π * c := by
    have h : 4 * π * IA = 4 * π * (π * c) := by rw [hsat]; ring
    exact mul_left_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < 4 * π)) h
  have hEq : 2 * IA = ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2) := by
    rw [hperim, hIAval]; ring
  exact fourierCoeff_eq_zero_of_wirtinger_saturation hf hg hfper hgper hab hEq

-- ============================================================
-- SECTION XIII: first-mode rigidity — the ellipse is a *circle*
--   (the surviving fundamental harmonic satisfies ĉ₁f = i·ĉ₁g, the 90°
--    rotation that upgrades the Section-XII ellipse to a genuine circle)
-- ============================================================

/-- **First-mode rigidity (pointwise).**  If the frequency-`1` Hurwitz deficit summand vanishes,

        ‖a‖² + ‖b‖² − 2·Im(a·conj b) = 0 ,

    then the two amplitudes are `90°` rotations of one another: `a = i·b`.  Writing
    `a = a.re + a.im·i`, `b = b.re + b.im·i`, the summand is an exact sum of squares

        ‖a‖² + ‖b‖² − 2·Im(a·conj b) = (a.im − b.re)² + (a.re + b.im)² ,

    so it vanishes iff `a.im = b.re` and `a.re = −b.im`, i.e. `a = i·b`.  This is the
    Cauchy–Schwarz / AM–GM equality signature of the circle at the fundamental frequency:
    `‖a‖ = ‖b‖` together with `a·conj b` purely imaginary and positive.  Combined with the
    vanishing of all higher modes (`fourierCoeff_eq_zero_of_wirtinger_saturation`), it pins the
    saturating curve to `t ↦ (a₀ + 2·Re(a·e^{it}), b₀ + 2·Re(b·e^{it}))` with `b = −i·a`, a
    circle of radius `2‖a‖`. -/
private theorem firstMode_rigidity (a b : ℂ)
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * conj b).im = 0) :
    a = Complex.I * b := by
  -- Expand the two norms and the imaginary cross term into real/imaginary parts.
  have hna : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnb : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have him : (a * conj b).im = a.im * b.re - a.re * b.im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [hna, hnb, him] at h
  -- The deficit is `(a.im − b.re)² + (a.re + b.im)²`, so each square vanishes.
  have hsq1 : (a.im - b.re) ^ 2 = 0 :=
    le_antisymm (by nlinarith [sq_nonneg (a.re + b.im), h]) (sq_nonneg _)
  have hsq2 : (a.re + b.im) ^ 2 = 0 :=
    le_antisymm (by nlinarith [sq_nonneg (a.im - b.re), h]) (sq_nonneg _)
  have e1 : a.im - b.re = 0 := by
    have := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq1; linarith [this]
  have e2 : a.re + b.im = 0 := by
    have := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq2; linarith [this]
  -- Read off `a = i·b` on real and imaginary parts.
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    linarith [e2]
  · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    linarith [e1]

/-- **Every Hurwitz deficit summand vanishes under Wirtinger saturation.**  If the analytic
    Wirtinger inequality is saturated,

        2 ∫₀^{2π} f·g'  =  ∫₀^{2π} ((f')² + (g')²) ,

    then for *every* frequency `n` the deficit summand is zero:

        n²‖ĉₙf‖² + n²‖ĉₙg‖² − 2n·Im(ĉₙf·conj ĉₙg)  =  0 .

    A nonnegative summable family (`area_deficit_summand_nonneg`) with total zero is termwise
    zero.  Section XII reads the `|n| ≥ 2` modes off this (they die); Section XIII reads off the
    surviving `n = 1` mode (it rotates).  This is the common analytic core of both. -/
private theorem deficit_summand_eq_zero_of_wirtinger_saturation
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π)
    (hEq : 2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x
            = ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) :
    ∀ n : ℤ, (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
        + (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2
        - 2 * (n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n *
            conj (fourierCoeffOn hab (ofReal ∘ g) n)).im = 0 := by
  have hdfc : Continuous (deriv f) := by
    have h := (contDiff_infty_iterate_deriv f hf 1).continuous
    rwa [Function.iterate_one] at h
  have hdgc : Continuous (deriv g) := by
    have h := (contDiff_infty_iterate_deriv g hg 1).continuous
    rwa [Function.iterate_one] at h
  have HSf := hasSum_nsq_normSq_fourierCoeffOn hf hfper hab
  have HSg := hasSum_nsq_normSq_fourierCoeffOn hg hgper hab
  have HSA := hasSum_fourier_area_formula hf.continuous hg hgper hab
  set If := ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 with hIf
  set Ig := ∫ x in (0 : ℝ)..(2 * π), (deriv g x) ^ 2 with hIg
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have HSdef := (HSf.add HSg).sub (HSA.mul_left 2)
  have hsplit : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = If + Ig := by
    rw [hIf, hIg]
    exact intervalIntegral.integral_add
      ((hdfc.pow 2).intervalIntegrable _ _) ((hdgc.pow 2).intervalIntegrable _ _)
  have hTzero : ((2 * π - 0)⁻¹ • If) + ((2 * π - 0)⁻¹ • Ig)
      - 2 * ((2 * π - 0)⁻¹ • IA) = 0 := by
    simp only [smul_eq_mul, sub_zero]
    rw [hsplit] at hEq
    have hfac : (2 * π)⁻¹ * If + (2 * π)⁻¹ * Ig - 2 * ((2 * π)⁻¹ * IA)
        = (2 * π)⁻¹ * (If + Ig - 2 * IA) := by ring
    rw [hfac, show If + Ig - 2 * IA = 0 from by linarith, mul_zero]
  rw [hTzero] at HSdef
  intro n
  have hle := le_hasSum HSdef n (fun m _ => by
    convert area_deficit_summand_nonneg (fourierCoeffOn hab (ofReal ∘ f) m)
      (fourierCoeffOn hab (ofReal ∘ g) m) m using 1; ring)
  have hge := area_deficit_summand_nonneg (fourierCoeffOn hab (ofReal ∘ f) n)
    (fourierCoeffOn hab (ofReal ∘ g) n) n
  exact le_antisymm (by nlinarith [hle]) hge

/-- **Equality case, fundamental mode — analytic form.**  If the analytic Wirtinger inequality
    is saturated, `2∫f·g' = ∫(f'²+g'²)`, the surviving first-harmonic amplitudes of the two
    coordinates are `90°` rotations of one another:

        ĉ₁(f)  =  i · ĉ₁(g) .

    The `n = 1` deficit summand `‖ĉ₁f‖² + ‖ĉ₁g‖² − 2·Im(ĉ₁f·conj ĉ₁g)` vanishes
    (`deficit_summand_eq_zero_of_wirtinger_saturation` at `n = 1`), and `firstMode_rigidity`
    turns that into the rotation identity.  Together with the higher modes dying
    (`fourierCoeff_eq_zero_of_wirtinger_saturation`), this is exactly the statement that the
    saturating curve is a circle — not merely the ellipse that vanishing high modes alone allow. -/
theorem fourierCoeff_first_mode_of_wirtinger_saturation
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π)
    (hEq : 2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x
            = ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) :
    fourierCoeffOn hab (ofReal ∘ f) 1
      = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1 := by
  have h1 := deficit_summand_eq_zero_of_wirtinger_saturation hf hg hfper hgper hab hEq 1
  push_cast at h1
  have h1' : ‖fourierCoeffOn hab (ofReal ∘ f) 1‖ ^ 2
      + ‖fourierCoeffOn hab (ofReal ∘ g) 1‖ ^ 2
      - 2 * (fourierCoeffOn hab (ofReal ∘ f) 1 *
          conj (fourierCoeffOn hab (ofReal ∘ g) 1)).im = 0 := by
    linear_combination h1
  exact firstMode_rigidity _ _ h1'

/-- **Equality case, fundamental mode — geometric constant-speed form.**  For smooth
    period-`2π` coordinates parametrized with *constant speed* `(f')² + (g')² = c`, if the
    isoperimetric bound `4π·A ≤ L² = (2π)²·c` is *attained*, `4π·∫f·g' = (2π)²·c`, then the
    fundamental harmonics are `90°` rotations: `ĉ₁(f) = i·ĉ₁(g)`.  This upgrades
    `fourierCoeff_eq_zero_of_isoperimetric_saturation` (which only kills the modes `|n| ≥ 2`,
    leaving an ellipse) to the rigidity that makes the curve a genuine circle. -/
theorem fourierCoeff_first_mode_of_isoperimetric_saturation
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c)
    (hsat : 4 * π * (∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) = (2 * π) ^ 2 * c) :
    fourierCoeffOn hab (ofReal ∘ f) 1
      = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1 := by
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have hperim : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = (2 * π) * c := by
    have hEqOn : Set.EqOn (fun x => (deriv f x) ^ 2 + (deriv g x) ^ 2) (fun _ => c)
        (Set.uIcc 0 (2 * π)) := fun x _ => hspeed x
    rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_const]
    simp
  have hIAval : IA = π * c := by
    have h : 4 * π * IA = 4 * π * (π * c) := by rw [hsat]; ring
    exact mul_left_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < 4 * π)) h
  have hEq : 2 * IA = ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2) := by
    rw [hperim, hIAval]; ring
  exact fourierCoeff_first_mode_of_wirtinger_saturation hf hg hfper hgper hab hEq

/-- **Full equality case of the Hurwitz isoperimetric inequality: saturation ⟹ the circle.**
    Let `f, g` be smooth period-`2π` coordinates parametrized with *constant speed*
    `(f')² + (g')² = c`, and suppose the isoperimetric bound is *attained*,
    `4π·A = (2π)²·c = L²`.  Then the entire Fourier spectrum collapses to the first harmonic,

      • `∀ n, |n| ≥ 2 → ĉₙ(f) = ĉₙ(g) = 0`  (no mode above the fundamental survives), and
      • `ĉ₁(f) = i·ĉ₁(g)`  (the surviving fundamental is a `90°` rotation),

    which together say `t ↦ (f(t), g(t))` traces a genuine **circle**: `f = ĉ₀f + 2·Re(ĉ₁f·e^{it})`,
    `g = ĉ₀g + 2·Re(ĉ₁g·e^{it})` with `ĉ₁g = −i·ĉ₁f`, i.e. a circle of radius `2‖ĉ₁f‖` centered at
    `(ĉ₀f, ĉ₀g)`.  This is the forward (⟹) direction of Hurwitz's *equality holds iff the curve
    is a circle*, now with the fundamental-mode rigidity that distinguishes the circle from the
    ellipse the higher-mode collapse alone would permit. -/
theorem curve_is_circle_of_isoperimetric_saturation
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c)
    (hsat : 4 * π * (∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) = (2 * π) ^ 2 * c) :
    (∀ n : ℤ, 2 ≤ n.natAbs →
        fourierCoeffOn hab (ofReal ∘ f) n = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) n = 0)
      ∧ fourierCoeffOn hab (ofReal ∘ f) 1
          = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1 :=
  ⟨fourierCoeff_eq_zero_of_isoperimetric_saturation hf hg hfper hgper hab hspeed hsat,
   fourierCoeff_first_mode_of_isoperimetric_saturation hf hg hfper hgper hab hspeed hsat⟩


-- ============================================================
-- SECTION XIV: the converse — the circle saturates (full IFF)
--   From the spectral signature of the circle (all modes |n| ≥ 2 dead and the
--   fundamental a 90° rotation ĉ₁f = i·ĉ₁g) we reconstruct Wirtinger equality
--   2∫f·g' = ∫(f'²+g'²), the backward (⟸) direction of Hurwitz's
--   "equality holds iff the curve is a circle".
-- ============================================================

/-- **Reality of the Fourier coefficients of a real function.**  For a real-valued `f`, the
    coefficient at frequency `-n` is the complex conjugate of the coefficient at `n`:

        conj (ĉₙ(f))  =  ĉ₋ₙ(f) .

    Both sides are `(b-a)⁻¹` times an interval integral; conjugation passes through the real
    scalar (`Complex.conj_ofReal`) and the integral (`integral_conj`), fixes the real integrand
    `f`, and sends the kernel `conj (fourier (-n) x) = fourier n x` (`fourier_neg`). -/
private theorem fourierCoeffOn_conj_neg {f : ℝ → ℝ} (hab : (0 : ℝ) < 2 * π) (n : ℤ) :
    conj (fourierCoeffOn hab (ofReal ∘ f) n) = fourierCoeffOn hab (ofReal ∘ f) (-n) := by
  rw [fourierCoeffOn_eq_integral (ofReal ∘ f) n hab,
      fourierCoeffOn_eq_integral (ofReal ∘ f) (-n) hab, neg_neg,
      Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
      ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, Function.comp_apply, fourier_neg,
    Complex.conj_conj]

/-- **Fundamental-mode deficit vanishes for a `90°` rotation (converse of `firstMode_rigidity`).**
    If `a = i·b` then the frequency-`1` Hurwitz summand is exactly `0`:

        ‖a‖² + ‖b‖² − 2·Im(a·conj b)  =  0 .

    Writing `a = i·b` gives `a.re = −b.im`, `a.im = b.re`, and the summand is the sum of squares
    `(a.im − b.re)² + (a.re + b.im)²`, which then collapses to `0`. -/
private theorem firstMode_deficit_zero (a b : ℂ) (h : a = Complex.I * b) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * conj b).im = 0 := by
  have hre : a.re = -b.im := by rw [h]; simp [Complex.mul_re]
  have him : a.im = b.re := by rw [h]; simp [Complex.mul_im]
  have hna : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnb : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have himx : (a * conj b).im = a.im * b.re - a.re * b.im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [hna, hnb, himx, hre, him]; ring

/-- **Every Hurwitz deficit summand vanishes on the spectral signature of the circle.**  If the
    Fourier spectrum of the coordinate pair `(f, g)` is that of a circle — all modes `|n| ≥ 2`
    dead and the fundamental a `90°` rotation `ĉ₁f = i·ĉ₁g` — then for *every* frequency `n`

        n²‖ĉₙf‖² + n²‖ĉₙg‖² − 2·(n·Im(ĉₙf·conj ĉₙg))  =  0 .

    The modes `|n| ≥ 2` die by hypothesis, `n = 0` is trivially `0`, `n = 1` is
    `firstMode_deficit_zero`, and `n = −1` reduces to the same via the reality relation
    `ĉ₋₁ = conj ĉ₁` (`fourierCoeffOn_conj_neg`). -/
private theorem deficit_summand_zero_of_spectrum
    {f g : ℝ → ℝ} (hab : (0 : ℝ) < 2 * π)
    (hhigh : ∀ m : ℤ, 2 ≤ m.natAbs →
        fourierCoeffOn hab (ofReal ∘ f) m = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) m = 0)
    (hone : fourierCoeffOn hab (ofReal ∘ f) 1
        = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1) :
    ∀ n : ℤ, (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
        + (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2
        - 2 * ((n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n *
            conj (fourierCoeffOn hab (ofReal ∘ g) n)).im) = 0 := by
  intro n
  by_cases hn2 : 2 ≤ n.natAbs
  · obtain ⟨hf0, hg0⟩ := hhigh n hn2
    rw [hf0, hg0]; simp
  · have hlo : -1 ≤ n := by omega
    have hhi : n ≤ 1 := by omega
    interval_cases n
    · -- n = -1
      have hrf : fourierCoeffOn hab (ofReal ∘ f) (-1)
          = conj (fourierCoeffOn hab (ofReal ∘ f) 1) := (fourierCoeffOn_conj_neg hab 1).symm
      have hrg : fourierCoeffOn hab (ofReal ∘ g) (-1)
          = conj (fourierCoeffOn hab (ofReal ∘ g) 1) := (fourierCoeffOn_conj_neg hab 1).symm
      rw [hrf, hrg]
      set a := fourierCoeffOn hab (ofReal ∘ f) 1 with ha
      set b := fourierCoeffOn hab (ofReal ∘ g) 1 with hb
      have hre : a.re = -b.im := by rw [hone]; simp [Complex.mul_re]
      have him : a.im = b.re := by rw [hone]; simp [Complex.mul_im]
      have hna : ‖(conj a)‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
        rw [Complex.norm_conj, Complex.sq_norm, Complex.normSq_apply]; ring
      have hnb : ‖(conj b)‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by
        rw [Complex.norm_conj, Complex.sq_norm, Complex.normSq_apply]; ring
      have himx : (conj a * conj (conj b)).im = -(a.im * b.re - a.re * b.im) := by
        simp only [Complex.conj_conj, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
      push_cast
      rw [hna, hnb, himx, hre, him]; ring
    · -- n = 0
      push_cast; ring
    · -- n = 1
      have hzero := firstMode_deficit_zero _ _ hone
      push_cast
      linear_combination hzero

/-- **Converse of the Hurwitz equality case (analytic Wirtinger form).**  If the Fourier
    spectrum of `(f, g)` is that of a circle — every mode `|n| ≥ 2` vanishes and the fundamental
    is a `90°` rotation `ĉ₁f = i·ĉ₁g` — then the analytic Wirtinger inequality is *saturated*:

        2 ∫₀^{2π} f·g'  =  ∫₀^{2π} ((f')² + (g')²) .

    Every Hurwitz deficit summand is `0` (`deficit_summand_zero_of_spectrum`), so the total
    deficit `(2π)⁻¹[∫(f'²+g'²) − 2∫f·g']` — which `HasSum`s that summable family
    (`hasSum_nsq_normSq_fourierCoeffOn` twice minus `2×` `hasSum_fourier_area_formula`) — is `0`.
    This is the backward (⟸) direction of `fourierCoeff_first_mode_of_wirtinger_saturation`
    together with `fourierCoeff_eq_zero_of_wirtinger_saturation`, completing the analytic
    equality-iff-circle. -/
theorem wirtinger_saturation_of_fourier_spectrum
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π)
    (hhigh : ∀ n : ℤ, 2 ≤ n.natAbs →
        fourierCoeffOn hab (ofReal ∘ f) n = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) n = 0)
    (hone : fourierCoeffOn hab (ofReal ∘ f) 1
        = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1) :
    2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x
      = ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2) := by
  have hdfc : Continuous (deriv f) := by
    have h := (contDiff_infty_iterate_deriv f hf 1).continuous
    rwa [Function.iterate_one] at h
  have hdgc : Continuous (deriv g) := by
    have h := (contDiff_infty_iterate_deriv g hg 1).continuous
    rwa [Function.iterate_one] at h
  have HSf := hasSum_nsq_normSq_fourierCoeffOn hf hfper hab
  have HSg := hasSum_nsq_normSq_fourierCoeffOn hg hgper hab
  have HSA := hasSum_fourier_area_formula hf.continuous hg hgper hab
  set If := ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 with hIf
  set Ig := ∫ x in (0 : ℝ)..(2 * π), (deriv g x) ^ 2 with hIg
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have HSdef := (HSf.add HSg).sub (HSA.mul_left 2)
  have hzero := deficit_summand_zero_of_spectrum hab hhigh hone
  -- the summable deficit family is identically zero, so its total is zero
  have hzsum : HasSum (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
        + (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2
        - 2 * ((n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n *
            conj (fourierCoeffOn hab (ofReal ∘ g) n)).im)) 0 := by
    rw [show (fun n : ℤ => (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
        + (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2
        - 2 * ((n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n *
            conj (fourierCoeffOn hab (ofReal ∘ g) n)).im))
        = (fun _ : ℤ => (0 : ℝ)) from funext hzero]
    exact hasSum_zero
  have hTot0 : ((2 * π - 0)⁻¹ • If) + ((2 * π - 0)⁻¹ • Ig)
      - 2 * ((2 * π - 0)⁻¹ • IA) = 0 := HSdef.unique hzsum
  -- clear the positive factor and recombine the perimeter integrals
  simp only [smul_eq_mul, sub_zero] at hTot0
  have hfac : (2 * π)⁻¹ * If + (2 * π)⁻¹ * Ig - 2 * ((2 * π)⁻¹ * IA)
      = (2 * π)⁻¹ * (If + Ig - 2 * IA) := by ring
  rw [hfac] at hTot0
  have hinv : (2 * π)⁻¹ ≠ (0 : ℝ) := by positivity
  have key : If + Ig - 2 * IA = 0 := by
    rcases mul_eq_zero.mp hTot0 with h | h
    · exact absurd h hinv
    · exact h
  have hsplit : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = If + Ig := by
    rw [hIf, hIg]
    exact intervalIntegral.integral_add
      ((hdfc.pow 2).intervalIntegrable _ _) ((hdgc.pow 2).intervalIntegrable _ _)
  rw [hsplit]
  linarith [key]

/-- **Analytic Hurwitz equality-iff-circle (Wirtinger form).**  For smooth (`C^∞`) period-`2π`
    real coordinates `f, g`, the analytic Wirtinger inequality is saturated,

        2 ∫₀^{2π} f·g'  =  ∫₀^{2π} ((f')² + (g')²) ,

    *if and only if* the Fourier spectrum is that of a circle: every mode `|n| ≥ 2` vanishes and
    the fundamental harmonic is a `90°` rotation `ĉ₁f = i·ĉ₁g`.  The forward direction is
    `fourierCoeff_eq_zero_of_wirtinger_saturation` (high modes die) together with
    `fourierCoeff_first_mode_of_wirtinger_saturation` (the fundamental rotates); the converse is
    `wirtinger_saturation_of_fourier_spectrum`.  This is the full analytic statement of Hurwitz's
    theorem that equality in the isoperimetric inequality holds exactly for the circle. -/
theorem wirtinger_saturation_iff_fourier_spectrum
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) :
    (2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x
        = ∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2))
      ↔ ((∀ n : ℤ, 2 ≤ n.natAbs →
            fourierCoeffOn hab (ofReal ∘ f) n = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) n = 0)
          ∧ fourierCoeffOn hab (ofReal ∘ f) 1
              = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1) := by
  constructor
  · intro hEq
    exact ⟨fourierCoeff_eq_zero_of_wirtinger_saturation hf hg hfper hgper hab hEq,
      fourierCoeff_first_mode_of_wirtinger_saturation hf hg hfper hgper hab hEq⟩
  · rintro ⟨hhigh, hone⟩
    exact wirtinger_saturation_of_fourier_spectrum hf hg hfper hgper hab hhigh hone



/-- **Converse of the Hurwitz equality case (geometric constant-speed form).**  For smooth
    period-`2π` coordinates parametrized with *constant speed* `(f')² + (g')² = c`, if the Fourier
    spectrum is that of a circle — every mode `|n| ≥ 2` dead and `ĉ₁f = i·ĉ₁g` — then the
    isoperimetric bound is *attained*:

        4π·A  =  4π·∫f·g'  =  (2π)²·c  =  L² .

    The Wirtinger converse `wirtinger_saturation_of_fourier_spectrum` gives `2∫f·g' = ∫(f'²+g'²)`,
    and constant speed turns `∫(f'²+g'²)` into `2π·c`, so `∫f·g' = π·c` and `4π·∫f·g' = (2π)²·c`. -/
theorem isoperimetric_saturation_of_fourier_spectrum
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c)
    (hhigh : ∀ n : ℤ, 2 ≤ n.natAbs →
        fourierCoeffOn hab (ofReal ∘ f) n = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) n = 0)
    (hone : fourierCoeffOn hab (ofReal ∘ f) 1
        = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1) :
    4 * π * (∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) = (2 * π) ^ 2 * c := by
  have hEq := wirtinger_saturation_of_fourier_spectrum hf hg hfper hgper hab hhigh hone
  have hperim : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = (2 * π) * c := by
    have hEqOn : Set.EqOn (fun x => (deriv f x) ^ 2 + (deriv g x) ^ 2) (fun _ => c)
        (Set.uIcc 0 (2 * π)) := fun x _ => hspeed x
    rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_const]
    simp
  rw [hperim] at hEq
  linear_combination (2 * π) * hEq

/-- **Geometric Hurwitz equality-iff-circle (constant-speed form).**  For smooth period-`2π`
    coordinates parametrized with *constant speed* `(f')² + (g')² = c`, the isoperimetric bound is
    *attained*,

        4π·A  =  4π·∫f·g'  =  (2π)²·c  =  L² ,

    *if and only if* the Fourier spectrum is that of a circle: every mode `|n| ≥ 2` vanishes and
    the fundamental harmonic is a `90°` rotation `ĉ₁f = i·ĉ₁g` — i.e. the curve
    `t ↦ (f(t), g(t))` is a genuine circle.  The forward direction is
    `curve_is_circle_of_isoperimetric_saturation`; the converse is
    `isoperimetric_saturation_of_fourier_spectrum`.  This is Hurwitz's classical theorem: among
    closed curves of a given length, equality in `L² ≥ 4πA` holds exactly for the circle. -/
theorem isoperimetric_saturation_iff_circle
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c) :
    (4 * π * (∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) = (2 * π) ^ 2 * c)
      ↔ ((∀ n : ℤ, 2 ≤ n.natAbs →
            fourierCoeffOn hab (ofReal ∘ f) n = 0 ∧ fourierCoeffOn hab (ofReal ∘ g) n = 0)
          ∧ fourierCoeffOn hab (ofReal ∘ f) 1
              = Complex.I * fourierCoeffOn hab (ofReal ∘ g) 1) := by
  constructor
  · intro hsat
    exact curve_is_circle_of_isoperimetric_saturation hf hg hfper hgper hab hspeed hsat
  · rintro ⟨hhigh, hone⟩
    exact isoperimetric_saturation_of_fourier_spectrum hf hg hfper hgper hab hspeed hhigh hone

-- ============================================================
-- SECTION XV: quantitative isoperimetric stability
--   (Bonnesen / Fuglede-type) — the deficit controls each higher harmonic
-- ============================================================

/-- **Quantitative isoperimetric stability — analytic (normalized) form.**  For smooth (`C^∞`)
    period-`2π` real coordinates `f, g` and any frequency `n` with `|n| ≥ 2`, the energy of the
    `n`-th Fourier harmonic is controlled by the *normalized* Hurwitz deficit:

        2·(‖ĉₙ(f)‖² + ‖ĉₙ(g)‖²)
          ≤  (2π)⁻¹ · [ ∫₀^{2π}((f')²+(g')²)  −  2 ∫₀^{2π} f·g' ] .

    This is a *quantitative* strengthening of the equality case
    `fourierCoeff_eq_zero_of_wirtinger_saturation`: rather than merely asserting that a
    *vanishing* deficit annihilates every mode above the first, it bounds each higher harmonic's
    amplitude by the *size* of the deficit — a Bonnesen/Fuglede-type stability estimate.
    Setting the deficit to `0` recovers `ĉₙf = ĉₙg = 0` for all `|n| ≥ 2` (spectral rigidity), so
    the qualitative "equality ⇒ circle" theorem is the degenerate case of this inequality.

    Proof.  The deficit is the total of the nonnegative `HasSum` `HSdef` whose frequency-`n`
    summand is `n²(‖ĉₙf‖²+‖ĉₙg‖²) − 2n·Im(ĉₙf·conj ĉₙg)`.  A single nonnegative term is `≤` the
    whole sum (`le_hasSum`), and the sharpened per-mode bound `area_deficit_summand_ge_gap`
    dominates that summand below by `(|n|²−|n|)(‖ĉₙf‖²+‖ĉₙg‖²)`; on `|n| ≥ 2` the coefficient
    `|n|²−|n| ≥ 2`, giving the stated factor `2`. -/
theorem two_mul_normSq_fourierCoeffOn_le_normalized_deficit
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : 2 ≤ n.natAbs) :
    2 * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
        + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
      ≤ (2 * π)⁻¹ * ((∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2))
          - 2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) := by
  have HSf := hasSum_nsq_normSq_fourierCoeffOn hf hfper hab
  have HSg := hasSum_nsq_normSq_fourierCoeffOn hg hgper hab
  have HSA := hasSum_fourier_area_formula hf.continuous hg hgper hab
  have HSdef := (HSf.add HSg).sub (HSA.mul_left 2)
  -- The frequency-`n` summand is `≤` the whole (nonnegative) deficit sum.
  have hle := le_hasSum HSdef n (fun m _ => by
    convert area_deficit_summand_nonneg
      (fourierCoeffOn hab (ofReal ∘ f) m) (fourierCoeffOn hab (ofReal ∘ g) m) m using 1
    ring)
  simp only [smul_eq_mul, sub_zero] at hle
  set a := fourierCoeffOn hab (ofReal ∘ f) n with ha
  set b := fourierCoeffOn hab (ofReal ∘ g) n with hb
  set If := ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 with hIf
  set Ig := ∫ x in (0 : ℝ)..(2 * π), (deriv g x) ^ 2 with hIg
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  -- Sharpened lower bound on the summand, and `|n|²−|n| ≥ 2` on the high band.
  have hgap := area_deficit_summand_ge_gap a b n
  have hm : (2 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (show (2 : ℤ) ≤ |n| by rw [Int.abs_eq_natAbs]; exact_mod_cast hn)
  have hcoef : (2 : ℝ) ≤ |(n : ℝ)| ^ 2 - |(n : ℝ)| := by
    nlinarith [hm, mul_nonneg (by linarith [hm] : (0 : ℝ) ≤ |(n : ℝ)| - 2)
      (by linarith [hm] : (0 : ℝ) ≤ |(n : ℝ)| + 1)]
  have hP : (0 : ℝ) ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by positivity
  have hstep : 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)
      ≤ (2 * π)⁻¹ * If + (2 * π)⁻¹ * Ig - 2 * ((2 * π)⁻¹ * IA) := by
    nlinarith [hle, hgap, hcoef, hP,
      mul_nonneg (by linarith [hcoef] : (0 : ℝ) ≤ |(n : ℝ)| ^ 2 - |(n : ℝ)| - 2) hP]
  -- Recombine into the normalized-deficit form; split the perimeter integral.
  have hcomb : (2 * π)⁻¹ * ((If + Ig) - 2 * IA)
      = (2 * π)⁻¹ * If + (2 * π)⁻¹ * Ig - 2 * ((2 * π)⁻¹ * IA) := by ring
  have hdfc : Continuous (deriv f) := by
    have h := (contDiff_infty_iterate_deriv f hf 1).continuous
    rwa [Function.iterate_one] at h
  have hdgc : Continuous (deriv g) := by
    have h := (contDiff_infty_iterate_deriv g hg 1).continuous
    rwa [Function.iterate_one] at h
  have hsplit : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = If + Ig := by
    rw [hIf, hIg]
    exact intervalIntegral.integral_add
      ((hdfc.pow 2).intervalIntegrable _ _) ((hdgc.pow 2).intervalIntegrable _ _)
  rw [hsplit, hcomb]
  exact hstep

/-- **Quantitative isoperimetric stability — geometric (Bonnesen/Fuglede) form.**  For a smooth
    period-`2π` closed curve `t ↦ (f(t), g(t))` parametrized with *constant speed*
    `(f')² + (g')² = c` — so its length is `L = 2π√c`, hence `L² = (2π)²·c`, and its enclosed
    area is `A = ∫₀^{2π} f·g'` — every Fourier harmonic above the first is controlled by the
    isoperimetric deficit `L² − 4πA`:

        2·(2π)²·(‖ĉₙ(f)‖² + ‖ĉₙ(g)‖²)  ≤  L² − 4πA        (for every `|n| ≥ 2`).

    In particular `L² − 4πA ≥ 0` (the isoperimetric inequality) and the deficit vanishes **iff**
    every higher harmonic vanishes — i.e. the curve is a circle
    (`isoperimetric_saturation_iff_circle`).  This inequality is the quantitative refinement: the
    *magnitude* of the deficit bounds the `L²`-distance of the curve from the nearest circle,
    mode by mode.  It is obtained from the normalized analytic bound
    `two_mul_normSq_fourierCoeffOn_le_normalized_deficit` by evaluating the constant-speed
    perimeter energy `∫((f')²+(g')²) = 2π·c` and scaling by `(2π)² > 0`. -/
theorem two_mul_normSq_fourierCoeffOn_le_isoperimetric_deficit
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c)
    (n : ℤ) (hn : 2 ≤ n.natAbs) :
    2 * (2 * π) ^ 2 * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
        + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
      ≤ (2 * π) ^ 2 * c - 4 * π * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x := by
  have hcore := two_mul_normSq_fourierCoeffOn_le_normalized_deficit hf hg hfper hgper hab n hn
  have hperim : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = (2 * π) * c := by
    have hEqOn : Set.EqOn (fun x => (deriv f x) ^ 2 + (deriv g x) ^ 2) (fun _ => c)
        (Set.uIcc 0 (2 * π)) := fun x _ => hspeed x
    rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_const]
    simp
  rw [hperim] at hcore
  set P := ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2 + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2 with hP
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have hpos : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcore (le_of_lt hpos)
  have h2πne : (2 * π) ≠ 0 := ne_of_gt hab
  have hRHS : (2 * π) ^ 2 * ((2 * π)⁻¹ * ((2 * π) * c - 2 * IA))
      = (2 * π) ^ 2 * c - 4 * π * IA := by
    field_simp
    ring
  rw [hRHS] at hmul
  have hLHS : (2 * π) ^ 2 * (2 * P) = 2 * (2 * π) ^ 2 * P := by ring
  rw [hLHS] at hmul
  exact hmul

-- ============================================================
-- SECTION XVI: aggregate (global) quantitative stability
--   — summing the per-mode Fuglede bounds into a single
--     L²-distance-to-circle estimate controlled by the deficit
-- ============================================================

/-- **Nonnegativity of the harmonic weight `|n|²−|n|`.**  For every integer `n`,
    `0 ≤ |n|² − |n|`.  The weight is `|n|·(|n|−1)`, which is `0` at `n = 0` and at
    `|n| = 1` (the mean and first harmonics — the circle modes) and strictly positive on
    `|n| ≥ 2`.  This is the coefficient in the aggregate stability sum. -/
private theorem deficit_gap_coef_nonneg (n : ℤ) :
    (0 : ℝ) ≤ |(n : ℝ)| ^ 2 - |(n : ℝ)| := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    nlinarith [h1]

/-- **Termwise domination of the deficit summand by the aggregate-stability summand.**  For
    the frequency-`n` Fourier coefficients `a = ĉₙ(f)`, `b = ĉₙ(g)`, the nonnegative gap term
    `(|n|²−|n|)(‖a‖²+‖b‖²)` lies below the `n`-th Hurwitz deficit summand
    `n²‖a‖²+n²‖b‖² − 2·(n·Im(a·conj b))`.  This is `area_deficit_summand_ge_gap` written in the
    exact shape of the deficit `HasSum` produced by `(HSf.add HSg).sub (HSA.mul_left 2)`, so it
    slots directly into the comparison test. -/
private theorem gap_le_deficit_summand {f g : ℝ → ℝ} (hab : (0 : ℝ) < 2 * π) (n : ℤ) :
    (|(n : ℝ)| ^ 2 - |(n : ℝ)|)
        * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
            + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
      ≤ ((n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
          + (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
        - 2 * ((n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n
            * conj (fourierCoeffOn hab (ofReal ∘ g) n)).im) := by
  calc (|(n : ℝ)| ^ 2 - |(n : ℝ)|)
          * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
              + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
        ≤ (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
            + (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2
            - 2 * (n : ℝ) * (fourierCoeffOn hab (ofReal ∘ f) n
                * conj (fourierCoeffOn hab (ofReal ∘ g) n)).im :=
          area_deficit_summand_ge_gap (fourierCoeffOn hab (ofReal ∘ f) n)
            (fourierCoeffOn hab (ofReal ∘ g) n) n
      _ = _ := by ring

/-- **Aggregate stability energy is summable.**  For smooth (`C^∞`) period-`2π` coordinates
    `f, g`, the frequency-weighted higher-harmonic energy

        ∑ₙ (|n|² − |n|)·(‖ĉₙ(f)‖² + ‖ĉₙ(g)‖²)

    converges.  The summand vanishes on the circle modes `n ∈ {−1, 0, 1}` (where `|n|²−|n| = 0`),
    so this is exactly the `H¹`-type squared distance of the curve from the family of circles.
    Summability follows from the comparison test: each term is nonnegative
    (`deficit_gap_coef_nonneg`) and dominated (`gap_le_deficit_summand`) by the `n`-th term of the
    convergent Hurwitz deficit series `(HSf.add HSg).sub (HSA.mul_left 2)`. -/
theorem summable_gap_normSq_fourierCoeffOn
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) :
    Summable (fun n : ℤ => (|(n : ℝ)| ^ 2 - |(n : ℝ)|)
        * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
            + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)) := by
  have HSf := hasSum_nsq_normSq_fourierCoeffOn hf hfper hab
  have HSg := hasSum_nsq_normSq_fourierCoeffOn hg hgper hab
  have HSA := hasSum_fourier_area_formula hf.continuous hg hgper hab
  have HSdef := (HSf.add HSg).sub (HSA.mul_left 2)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => gap_le_deficit_summand hab n)
    HSdef.summable
  exact mul_nonneg (deficit_gap_coef_nonneg n) (by positivity)

/-- **Aggregate (global) quantitative isoperimetric stability — analytic form.**  For smooth
    (`C^∞`) period-`2π` real coordinates `f, g` of a closed plane curve, the *entire*
    higher-harmonic energy is bounded by the normalized Hurwitz deficit:

        ∑ₙ (|n|² − |n|)·(‖ĉₙ(f)‖² + ‖ĉₙ(g)‖²)
          ≤  (2π)⁻¹ · [ ∫₀^{2π}((f')²+(g')²) − 2 ∫₀^{2π} f·g' ] .

    This is the global companion of the per-mode bound
    `two_mul_normSq_fourierCoeffOn_le_normalized_deficit`: instead of controlling one harmonic at
    a time, it sums the sharp per-mode gaps into a single inequality.  Because the weight
    `|n|²−|n|` vanishes for `n ∈ {−1, 0, 1}`, the left side is precisely the squared
    `L²`/`H¹`-distance of the curve from the family of circles, accumulated over *all* modes at
    once.  Setting the deficit to `0` forces every higher harmonic to vanish
    (`isoperimetric_saturation_iff_circle`), recovering the rigidity theorem as the degenerate
    `deficit = 0` case.

    Proof.  The right side is the total of the nonnegative Hurwitz deficit `HasSum`
    `HSdef := (HSf.add HSg).sub (HSA.mul_left 2)`.  Termwise the aggregate summand is nonnegative
    (`deficit_gap_coef_nonneg`) and `≤` the deficit summand (`gap_le_deficit_summand`), so the
    comparison test gives summability (`summable_gap_normSq_fourierCoeffOn`) and `tsum_le_tsum`
    dominates the aggregate tsum by the deficit total; rewriting the total into normalized form
    (clearing the `(2π)⁻¹` scaling and splitting the perimeter integral) finishes. -/
theorem tsum_gap_normSq_fourierCoeffOn_le_normalized_deficit
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) :
    ∑' n : ℤ, (|(n : ℝ)| ^ 2 - |(n : ℝ)|)
        * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
            + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
      ≤ (2 * π)⁻¹ * ((∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2))
          - 2 * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x) := by
  have HSf := hasSum_nsq_normSq_fourierCoeffOn hf hfper hab
  have HSg := hasSum_nsq_normSq_fourierCoeffOn hg hgper hab
  have HSA := hasSum_fourier_area_formula hf.continuous hg hgper hab
  have HSdef := (HSf.add HSg).sub (HSA.mul_left 2)
  have hsum_gap := summable_gap_normSq_fourierCoeffOn hf hg hfper hgper hab
  have hcmp := Summable.tsum_le_tsum (fun n => gap_le_deficit_summand hab n) hsum_gap
    HSdef.summable
  rw [HSdef.tsum_eq] at hcmp
  simp only [smul_eq_mul, sub_zero] at hcmp
  set If := ∫ x in (0 : ℝ)..(2 * π), (deriv f x) ^ 2 with hIf
  set Ig := ∫ x in (0 : ℝ)..(2 * π), (deriv g x) ^ 2 with hIg
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have hdfc : Continuous (deriv f) := by
    have h := (contDiff_infty_iterate_deriv f hf 1).continuous
    rwa [Function.iterate_one] at h
  have hdgc : Continuous (deriv g) := by
    have h := (contDiff_infty_iterate_deriv g hg 1).continuous
    rwa [Function.iterate_one] at h
  have hsplit : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = If + Ig := by
    rw [hIf, hIg]
    exact intervalIntegral.integral_add
      ((hdfc.pow 2).intervalIntegrable _ _) ((hdgc.pow 2).intervalIntegrable _ _)
  rw [hsplit]
  have hcomb : (2 * π)⁻¹ * ((If + Ig) - 2 * IA)
      = (2 * π)⁻¹ * If + (2 * π)⁻¹ * Ig - 2 * ((2 * π)⁻¹ * IA) := by ring
  rw [hcomb]
  exact hcmp

/-- **Aggregate (global) quantitative isoperimetric stability — geometric (Bonnesen/Fuglede)
    form.**  For a smooth period-`2π` closed curve `t ↦ (f(t), g(t))` parametrized with
    *constant speed* `(f')² + (g')² = c` — so `L² = (2π)²·c` and `A = ∫₀^{2π} f·g'` — the total
    higher-harmonic energy is controlled by the isoperimetric deficit `L² − 4πA`:

        (2π)² · ∑ₙ (|n|² − |n|)·(‖ĉₙ(f)‖² + ‖ĉₙ(g)‖²)  ≤  L² − 4πA .

    The left side is `(2π)²` times the squared distance of the curve from the family of circles
    (the weight `|n|²−|n|` kills the three circle modes `n ∈ {−1,0,1}`), so this is the sharp
    *global* stability statement: the isoperimetric deficit dominates the total `L²`-deviation of
    the curve from a circle, all harmonics summed.  In particular `L² − 4πA ≥ 0`, with equality
    **iff** every higher harmonic vanishes — the circle (`isoperimetric_saturation_iff_circle`).

    Proof.  Scale the analytic aggregate bound
    `tsum_gap_normSq_fourierCoeffOn_le_normalized_deficit` by `(2π)² > 0`, evaluate the
    constant-speed perimeter energy `∫((f')²+(g')²) = 2π·c`, and simplify
    `(2π)²·(2π)⁻¹ = 2π`. -/
theorem tsum_gap_normSq_fourierCoeffOn_le_isoperimetric_deficit
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfper : ∀ t, f (t + 2 * π) = f t) (hgper : ∀ t, g (t + 2 * π) = g t)
    (hab : (0 : ℝ) < 2 * π) {c : ℝ}
    (hspeed : ∀ t, (deriv f t) ^ 2 + (deriv g t) ^ 2 = c) :
    (2 * π) ^ 2 * ∑' n : ℤ, (|(n : ℝ)| ^ 2 - |(n : ℝ)|)
        * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
            + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2)
      ≤ (2 * π) ^ 2 * c - 4 * π * ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x := by
  have hcore := tsum_gap_normSq_fourierCoeffOn_le_normalized_deficit hf hg hfper hgper hab
  have hperim : (∫ x in (0 : ℝ)..(2 * π), ((deriv f x) ^ 2 + (deriv g x) ^ 2)) = (2 * π) * c := by
    have hEqOn : Set.EqOn (fun x => (deriv f x) ^ 2 + (deriv g x) ^ 2) (fun _ => c)
        (Set.uIcc 0 (2 * π)) := fun x _ => hspeed x
    rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_const]
    simp
  rw [hperim] at hcore
  set S := ∑' n : ℤ, (|(n : ℝ)| ^ 2 - |(n : ℝ)|)
      * (‖fourierCoeffOn hab (ofReal ∘ f) n‖ ^ 2
          + ‖fourierCoeffOn hab (ofReal ∘ g) n‖ ^ 2) with hS
  set IA := ∫ x in (0 : ℝ)..(2 * π), f x * deriv g x with hIA
  have hpos : (0 : ℝ) < (2 * π) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcore (le_of_lt hpos)
  have h2πne : (2 * π) ≠ 0 := ne_of_gt hab
  have hRHS : (2 * π) ^ 2 * ((2 * π)⁻¹ * ((2 * π) * c - 2 * IA))
      = (2 * π) ^ 2 * c - 4 * π * IA := by
    field_simp
    ring
  rw [hRHS] at hmul
  exact hmul

end IsoperimetricFourier
