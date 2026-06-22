import Mathlib

/-
# L'Hôpital's Rule via Taylor / Leading-Order Expansion (OQ-04)

The parent gallery entry `LHopital` proves L'Hôpital's rule for the `0/0` form
through the Mean Value Theorem (Mathlib's `HasDerivAt.lhopital_zero_right`). The
open question OQ-04 asks for the *Taylor-series* perspective instead: if `f` and
`g` both vanish at `a`, then near `a` they behave like their leading (linear)
Taylor terms, so

    f(x)/g(x) → f'(a)/g'(a).

This file formalizes exactly that derivation, **without** invoking the MVT-based
rule. The engine is the leading-order coefficient extraction

    f(a) = 0,  f differentiable at a  ⟹  f(x)/(x-a) → f'(a),

which is nothing but the definition of the derivative as the limit of slopes
(Mathlib's `HasDerivAt.tendsto_slope`). Writing

    f(x)/g(x) = (f(x)/(x-a)) / (g(x)/(x-a))    (for x ≠ a)

and dividing the two leading-order limits gives the rule directly. This is the
order-1 Taylor statement: the limit is the ratio of the first Taylor coefficients
`f'(a)/1!` and `g'(a)/1!`.

Self-contained: imports only Mathlib.
-/

namespace LHopitalOQ04

open Filter Topology

/-- **Leading-order Taylor coefficient.** If `f` vanishes at `a` and is
differentiable there, then `f(x)/(x-a) → f'(a)` as `x → a` (`x ≠ a`). This is the
derivative-as-slope statement specialised to `f a = 0`, and the `n = 1` case of the
Taylor expansion `f(x) = f'(a)(x-a) + o(x-a)`. -/
theorem tendsto_div_sub_of_hasDerivAt {f : ℝ → ℝ} {a f' : ℝ}
    (hf : HasDerivAt f f' a) (hfa : f a = 0) :
    Tendsto (fun x => f x / (x - a)) (𝓝[≠] a) (𝓝 f') := by
  apply hf.tendsto_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rw [slope_def_field, hfa, sub_zero]

/-- **L'Hôpital's rule for `0/0`, via the Taylor / leading-order route.** For `f, g`
differentiable at `a` with `f a = g a = 0` and `g'(a) ≠ 0`,

    f(x)/g(x) → f'(a)/g'(a)    as x → a.

The proof divides the two leading-order limits `f(x)/(x-a) → f'(a)` and
`g(x)/(x-a) → g'(a)`, using `f(x)/g(x) = (f(x)/(x-a))/(g(x)/(x-a))` for `x ≠ a`.
No Mean Value Theorem is used. -/
theorem lhopital_zero_taylor {f g : ℝ → ℝ} {a f' g' : ℝ}
    (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a)
    (hfa : f a = 0) (hga : g a = 0) (hg' : g' ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 (f' / g')) := by
  have hF := tendsto_div_sub_of_hasDerivAt hf hfa
  have hG := tendsto_div_sub_of_hasDerivAt hg hga
  have hdiv := hF.div hG hg'
  apply hdiv.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr hx
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hxa]

/-- The same statement packaged so the limit is named by the Taylor coefficients
`f'(a)/1!` and `g'(a)/1!` — making explicit that order-1 L'Hôpital *is* the ratio
of first Taylor coefficients. -/
theorem lhopital_zero_taylor_coeff {f g : ℝ → ℝ} {a f' g' : ℝ}
    (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a)
    (hfa : f a = 0) (hga : g a = 0) (hg' : g' ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a)
      (𝓝 ((f' / (Nat.factorial 1 : ℝ)) / (g' / (Nat.factorial 1 : ℝ)))) := by
  have h := lhopital_zero_taylor hf hg hfa hga hg'
  simpa using h

/-- Worked example: `sin x / x → 1` as `x → 0`. Here `f = sin` (with `f 0 = 0`,
`f'(0) = cos 0 = 1`) and `g = id` (`g 0 = 0`, `g'(0) = 1`), so the limit is
`cos 0 / 1 = 1`. -/
example : Tendsto (fun x => Real.sin x / x) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h := lhopital_zero_taylor (Real.hasDerivAt_sin 0) (hasDerivAt_id (0 : ℝ))
    Real.sin_zero rfl (by norm_num)
  simpa [Real.cos_zero] using h

/-- Worked example with a vanishing numerator derivative: `(1 - cos x)/x → 0` as
`x → 0`. Here `f'(0) = sin 0 = 0`, so the leading term vanishes and the limit is
`0 / 1 = 0`. -/
example : Tendsto (fun x => (1 - Real.cos x) / x) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hf : HasDerivAt (fun x => 1 - Real.cos x) (Real.sin 0) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (Real.hasDerivAt_cos 0)
  have h := lhopital_zero_taylor hf (hasDerivAt_id (0 : ℝ))
    (by simp) rfl (by norm_num)
  simpa using h

#check @lhopital_zero_taylor

end LHopitalOQ04
