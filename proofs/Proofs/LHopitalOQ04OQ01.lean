import Mathlib

/-
# Iterated L'Hôpital via the n-th Taylor Coefficient (OQ-04 → OQ-01)

The parent gallery entry `LHopitalOQ04` proves the **order-1** Taylor form of
L'Hôpital's rule: if `f a = g a = 0` and `g'(a) ≠ 0`, then near `a` both functions
behave like their linear Taylor terms, so

    f(x)/g(x) → f'(a)/g'(a).

This file generalizes that to **arbitrary order `n`**. Suppose `f` and `g` vanish at
`a` together with all of their derivatives up to order `n - 1`, and `g^(n)(a) ≠ 0`.
Then the ratio is governed by the first surviving Taylor coefficients:

    f(x)/g(x) → f^(n)(a) / g^(n)(a).

The engine is the **coefficient-extraction limit**

    f^(k)(a) = 0  for k < n   ⟹   f(x)/(x-a)^n → f^(n)(a)/n!,

which is Taylor's theorem with a little-o remainder (Mathlib's `Real.taylor_tendsto`)
after collapsing the degree-`n` Taylor polynomial to its single surviving top monomial
`(f^(n)(a)/n!)·(x-a)^n`. Dividing the two coefficient limits and cancelling the shared
`(x-a)^n` gives the rule — exactly as the parent divides two order-1 limits and cancels
`(x-a)`. No Mean Value Theorem is used; the deepest content of L'Hôpital's rule is made
explicit: the `0/0` limit is a **ratio of Taylor coefficients**.

At `n = 1` this recovers the parent statement. The `n = 2` example
`(1 - cos x)/x² → 1/2` exhibits a genuinely second-order `0/0` form (numerator and
denominator both vanish to order 2), where a single application of order-1 L'Hôpital is
still indeterminate.

Self-contained: imports only Mathlib.
-/

namespace LHopitalOQ04OQ01

open Filter Topology Nat

/-- **Collapse of the Taylor polynomial under vanishing lower derivatives.**
If `f^(k)(a) = 0` for every `k < n`, then the degree-`n` Taylor polynomial of `f` based
at `a` reduces to its single top monomial:

    taylorWithinEval f n univ a x = (n!)⁻¹ · (x-a)^n · f^(n)(a).

The proof expands `taylorWithinEval` into the finite sum `∑_{k≤n} (k!)⁻¹(x-a)^k f^(k)(a)`
(`taylor_within_apply`, over `Set.univ` so `iteratedDerivWithin = iteratedDeriv`), splits
off the `k = n` term, and observes every `k < n` term carries the vanishing factor
`f^(k)(a) = 0`. -/
theorem taylorWithinEval_collapse {f : ℝ → ℝ} {a x : ℝ} {n : ℕ}
    (hvanish : ∀ k < n, iteratedDeriv k f a = 0) :
    taylorWithinEval f n Set.univ a x
      = (n ! : ℝ)⁻¹ * (x - a) ^ n * iteratedDeriv n f a := by
  rw [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ, smul_eq_mul]
  have hz : (∑ k ∈ Finset.range n,
      ((k ! : ℝ)⁻¹ * (x - a) ^ k) • iteratedDerivWithin k f Set.univ a) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [iteratedDerivWithin_univ, hvanish k (Finset.mem_range.mp hk), smul_zero]
  rw [hz, zero_add]

/-- **The `n`-th Taylor coefficient as a limit.** If `f` is `n`-times continuously
differentiable and `f^(k)(a) = 0` for every `k < n`, then

    f(x)/(x-a)^n → f^(n)(a)/n!    as x → a  (x ≠ a).

This is the heart of the iterated rule: it extracts the leading (order-`n`) Taylor
coefficient of `f` at `a` as a genuine two-sided limit. Proof: Taylor's theorem gives
`(f x - taylorWithinEval f n univ a x)/(x-a)^n → 0`; the polynomial collapses to
`(f^(n)(a)/n!)(x-a)^n` (`taylorWithinEval_collapse`), which contributes exactly the
constant `f^(n)(a)/n!` after dividing by `(x-a)^n`. -/
theorem tendsto_div_pow_of_iteratedDeriv {f : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hf : ContDiff ℝ n f) (hvanish : ∀ k < n, iteratedDeriv k f a = 0) :
    Tendsto (fun x => f x / (x - a) ^ n) (𝓝[≠] a) (𝓝 (iteratedDeriv n f a / (n ! : ℝ))) := by
  -- Taylor's theorem with little-o remainder, along `𝓝[univ] a = 𝓝 a`.
  have htaylor := Real.taylor_tendsto (convex_univ) (Set.mem_univ a) hf.contDiffOn
  rw [nhdsWithin_univ] at htaylor
  -- Restrict the limit to the punctured neighbourhood `𝓝[≠] a ≤ 𝓝 a`.
  have htaylor' : Tendsto
      (fun x => (f x - taylorWithinEval f n Set.univ a x) / (x - a) ^ n)
      (𝓝[≠] a) (𝓝 0) :=
    htaylor.mono_left nhdsWithin_le_nhds
  have hfact : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  -- Add the constant `f^(n)(a)/n!`; the sum tends to `0 + f^(n)(a)/n!`.
  have hlim : Tendsto
      (fun x => (f x - taylorWithinEval f n Set.univ a x) / (x - a) ^ n
        + iteratedDeriv n f a / (n ! : ℝ))
      (𝓝[≠] a) (𝓝 (0 + iteratedDeriv n f a / (n ! : ℝ))) :=
    htaylor'.add tendsto_const_nhds
  rw [zero_add] at hlim
  -- On `𝓝[≠] a` this sum equals `f(x)/(x-a)^n`.
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr (by simpa using hx)
  have hd : (x - a) ^ n ≠ 0 := pow_ne_zero n hxa
  rw [taylorWithinEval_collapse hvanish]
  field_simp
  ring

/-- **Iterated L'Hôpital's rule for `0/0`, as a ratio of `n`-th Taylor coefficients.**
For `f, g` that are `n`-times continuously differentiable at `a`, with

    f^(k)(a) = g^(k)(a) = 0   for all k < n,   g^(n)(a) ≠ 0,

we have

    f(x)/g(x) → f^(n)(a) / g^(n)(a)    as x → a.

The proof divides the two coefficient limits `f(x)/(x-a)^n → f^(n)(a)/n!` and
`g(x)/(x-a)^n → g^(n)(a)/n!` (both from `tendsto_div_pow_of_iteratedDeriv`) and cancels
the common `(x-a)^n`, using `g^(n)(a) ≠ 0` for the nonzero denominator. The two `1/n!`
factors cancel, leaving the pure ratio of `n`-th derivatives. This is the exact
order-`n` analogue of the parent's `lhopital_zero_taylor`. -/
theorem lhopital_zero_taylor_iterated {f g : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hfv : ∀ k < n, iteratedDeriv k f a = 0)
    (hgv : ∀ k < n, iteratedDeriv k g a = 0)
    (hgn : iteratedDeriv n g a ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a)
      (𝓝 (iteratedDeriv n f a / iteratedDeriv n g a)) := by
  have hF := tendsto_div_pow_of_iteratedDeriv hf hfv
  have hG := tendsto_div_pow_of_iteratedDeriv hg hgv
  have hfact : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hgn' : iteratedDeriv n g a / (n ! : ℝ) ≠ 0 := div_ne_zero hgn hfact
  have hdiv := hF.div hG hgn'
  -- The limit value `(f^(n)/n!)/(g^(n)/n!)` collapses to `f^(n)/g^(n)`.
  rw [div_div_div_cancel_right₀ hfact] at hdiv
  apply hdiv.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr (by simpa using hx)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (pow_ne_zero n hxa)]

/-- The same statement packaged so the limit is *named* by the ratio of `n`-th Taylor
coefficients `f^(n)(a)/n!` and `g^(n)(a)/n!` — making explicit that order-`n` L'Hôpital
*is* the ratio of the first surviving Taylor coefficients. -/
theorem lhopital_zero_taylor_iterated_coeff {f g : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hfv : ∀ k < n, iteratedDeriv k f a = 0)
    (hgv : ∀ k < n, iteratedDeriv k g a = 0)
    (hgn : iteratedDeriv n g a ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a)
      (𝓝 ((iteratedDeriv n f a / (n ! : ℝ)) / (iteratedDeriv n g a / (n ! : ℝ)))) := by
  have hfact : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  rw [div_div_div_cancel_right₀ hfact]
  exact lhopital_zero_taylor_iterated hf hg hfv hgv hgn

/-! ### Worked example: `(1 - cos x)/x² → 1/2` (a genuine `n = 2` case) -/

/-- Derivative of the numerator `x ↦ 1 - cos x` is `x ↦ sin x`. -/
private theorem deriv_one_sub_cos : deriv (fun x : ℝ => 1 - Real.cos x) = fun x => Real.sin x := by
  funext x
  have : HasDerivAt (fun x : ℝ => 1 - Real.cos x) (Real.sin x) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x)
  exact this.deriv

/-- Derivative of `x ↦ x²` is `x ↦ 2x`. -/
private theorem deriv_sq : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
  funext x
  have : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  exact this.deriv

/-- Worked example: `(1 - cos x)/x² → 1/2` as `x → 0`. Both numerator and denominator
vanish to order 2 (`f(0) = f'(0) = 0`, `g(0) = g'(0) = 0`), so single-step L'Hôpital is
still `0/0`; the second-order rule gives the limit `f''(0)/g''(0) = 1/2`. -/
example : Tendsto (fun x => (1 - Real.cos x) / x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by
  set f : ℝ → ℝ := fun x => 1 - Real.cos x with hf_def
  set g : ℝ → ℝ := fun x => x ^ 2 with hg_def
  -- Smoothness.
  have hf : ContDiff ℝ 2 f := contDiff_const.sub Real.contDiff_cos
  have hg : ContDiff ℝ 2 g := contDiff_id.pow 2
  -- Second derivatives at 0.
  have hf2 : iteratedDeriv 2 f 0 = 1 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hf_def, deriv_one_sub_cos]
    have : HasDerivAt (fun x : ℝ => Real.sin x) (Real.cos 0) 0 := Real.hasDerivAt_sin 0
    rw [this.deriv, Real.cos_zero]
  have hg2 : iteratedDeriv 2 g 0 = 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hg_def, deriv_sq]
    have : HasDerivAt (fun x : ℝ => 2 * x) 2 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
    rw [this.deriv]
  -- Vanishing of the lower derivatives.
  have hfv : ∀ k < 2, iteratedDeriv k f 0 = 0 := by
    intro k hk
    interval_cases k
    · rw [iteratedDeriv_zero, hf_def]; simp
    · rw [iteratedDeriv_one, hf_def, deriv_one_sub_cos]; simp
  have hgv : ∀ k < 2, iteratedDeriv k g 0 = 0 := by
    intro k hk
    interval_cases k
    · rw [iteratedDeriv_zero, hg_def]; simp
    · rw [iteratedDeriv_one, hg_def, deriv_sq]; simp
  have hgn : iteratedDeriv 2 g 0 ≠ 0 := by rw [hg2]; norm_num
  have h := lhopital_zero_taylor_iterated hf hg hfv hgv hgn
  rw [hf2, hg2] at h
  simpa using h

#check @lhopital_zero_taylor_iterated

end LHopitalOQ04OQ01
