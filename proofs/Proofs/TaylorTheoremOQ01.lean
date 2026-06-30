import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

/-!
# Multivariate Taylor's Theorem via Restriction to a Line (Taylor #35, OQ-01)

## The Open Question
The parent entry (Taylor's theorem, Wiedijk #35) asks:

> *Can Lean formalize the multivariate Taylor theorem with remainder?*

The fully general statement expresses the `k`-th term of the expansion as a symmetric
`k`-linear map applied to `k` copies of the displacement vector (multi-index notation).
That packaging is genuinely heavy. This entry establishes the **standard reduction** that
underlies every proof of multivariate Taylor: restrict `f : E → ℝ` to the line segment
`t ↦ f(a + t • v)` and apply the one-dimensional Taylor theorem already in Mathlib.

## What This Proves
For a normed real vector space `E` and `f : E → ℝ`, define the *line restriction*
`g(t) = f(a + t • v)`. Then:

* `restriction_contDiff` — `g` inherits the smoothness of `f` (composition with the affine
  map `t ↦ a + t • v`);
* `restriction_hasDerivAt` / `restriction_deriv` — the first derivative of `g` is the
  directional (Fréchet) derivative: `g'(t) = Df(a + t•v)(v)`;
* `multivariate_taylor_lagrange` — the multivariate Taylor expansion with Lagrange
  remainder, with each term carried by the iterated derivative of the restriction
  (the directional-derivative form):
  `f(a+v) = T_n g(0) + g^{(n+1)}(θ)/(n+1)!` for some `θ ∈ (0,1)`;
* `multivariate_taylor_first_order` — the headline `n = 0` case, the multivariate mean
  value theorem in Lagrange form with the gradient made explicit:
  `f(a+v) = f(a) + Df(a + θ•v)(v)` for some `θ ∈ (0,1)`.

## Honest Scope
The remainder here is expressed through the iterated derivative of the one-dimensional
restriction `g`, i.e. the iterated **directional** derivative along `v`. The fully
symmetric-multilinear / multi-index packaging asked for in the open question (writing
`g^{(k)}(0)` as `D^k f(a)(v,…,v)` via `iteratedFDeriv`) is left as future work: it requires
the bridge `iteratedDeriv k g t = iteratedFDeriv ℝ k f (a+t•v) (fun _ => v)`, an induction
over the chain rule that we do not carry out here. The first-order term *is* given the
explicit Fréchet-derivative form, so the headline result is fully multivariate.

## Approach
- **Foundation (Mathlib):** `taylor_mean_remainder_lagrange_iteratedDeriv` (1-D Taylor with
  Lagrange remainder), the chain rule `HasFDerivAt.comp_hasDerivAt`, and `ContDiff.comp`.
- **Key Insight:** multivariate Taylor is one-dimensional Taylor applied to the restriction
  of `f` to a line; smoothness and the first derivative transfer through composition with
  the affine parametrisation `t ↦ a + t • v`.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Builds on Mathlib's 1-D Taylor theorem
- [x] Multivariate first-order Lagrange form with explicit Fréchet derivative
-/

namespace MultivariateTaylor

open Set Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The restriction of `f : E → ℝ` to the line through `a` in direction `v`,
viewed as a one-variable function `g(t) = f(a + t • v)`. -/
noncomputable def restriction (f : E → ℝ) (a v : E) : ℝ → ℝ := fun t => f (a + t • v)

@[simp] theorem restriction_apply (f : E → ℝ) (a v : E) (t : ℝ) :
    restriction f a v t = f (a + t • v) := rfl

@[simp] theorem restriction_zero (f : E → ℝ) (a v : E) :
    restriction f a v 0 = f a := by simp [restriction]

@[simp] theorem restriction_one (f : E → ℝ) (a v : E) :
    restriction f a v 1 = f (a + v) := by simp [restriction]

/-- The affine parametrisation `t ↦ a + t • v` is `HasDerivAt` with derivative `v`. -/
theorem line_hasDerivAt (a v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => a + s • v) v t := by
  simpa using (((hasDerivAt_id t).smul_const v).const_add a)

/-- The line restriction inherits the smoothness of `f`. -/
theorem restriction_contDiff {N : WithTop ℕ∞} (f : E → ℝ) (a v : E)
    (hf : ContDiff ℝ N f) : ContDiff ℝ N (restriction f a v) := by
  have hline : ContDiff ℝ N (fun s : ℝ => a + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact hf.comp hline

/-- **First directional derivative.** The derivative of the line restriction `g(t)` is the
Fréchet derivative of `f` applied to the direction `v`. -/
theorem restriction_hasDerivAt (f : E → ℝ) (a v : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (a + t • v)) :
    HasDerivAt (restriction f a v) (fderiv ℝ f (a + t • v) v) t := by
  have := hf.hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt a v t)
  simpa [restriction, Function.comp] using this

/-- The derivative of the line restriction, in `deriv` form. -/
theorem restriction_deriv (f : E → ℝ) (a v : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (a + t • v)) :
    deriv (restriction f a v) t = fderiv ℝ f (a + t • v) v :=
  (restriction_hasDerivAt f a v t hf).deriv

/-- **Multivariate Taylor's theorem with Lagrange remainder.**

For `f : E → ℝ` that is `(n+1)`-times continuously differentiable, the value `f(a + v)`
equals the degree-`n` Taylor polynomial of the line restriction `g(t) = f(a + t • v)`,
plus a Lagrange remainder `g^{(n+1)}(θ)/(n+1)!` for some `θ ∈ (0,1)`. The remainder is
carried by the iterated derivative of the restriction, i.e. the iterated directional
derivative along `v`. -/
theorem multivariate_taylor_lagrange {n : ℕ} (f : E → ℝ) (a v : E)
    (hf : ContDiff ℝ (n + 1) f) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      f (a + v) - taylorWithinEval (restriction f a v) n (Icc 0 1) 0 1 =
        iteratedDeriv (n + 1) (restriction f a v) θ / (n + 1)! := by
  have hg : ContDiff ℝ (n + 1) (restriction f a v) := restriction_contDiff f a v hf
  obtain ⟨θ, hθ, hEq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := restriction f a v)
      (x := 1) (x₀ := 0) (n := n) (by norm_num) hg.contDiffOn
  exact ⟨θ, hθ, by simpa using hEq⟩

/-- **Multivariate mean value / first-order Taylor theorem with Lagrange remainder.**

For `f : E → ℝ` continuously differentiable, there is an interior point `a + θ • v`
(`θ ∈ (0,1)`) at which the Fréchet derivative recovers the increment exactly:
`f(a + v) = f(a) + Df(a + θ•v)(v)`. This is the multivariate analogue of the
one-dimensional `f(b) - f(a) = f'(ξ)(b - a)`. -/
theorem multivariate_taylor_first_order (f : E → ℝ) (a v : E) (hf : ContDiff ℝ 1 f) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, f (a + v) = f a + fderiv ℝ f (a + θ • v) v := by
  obtain ⟨θ, hθ, hEq⟩ := multivariate_taylor_lagrange (n := 0) f a v (by simpa using hf)
  refine ⟨θ, hθ, ?_⟩
  have hdiff : DifferentiableAt ℝ f (a + θ • v) := (hf.differentiable le_rfl).differentiableAt
  rw [taylor_within_zero_eval, iteratedDeriv_one,
    restriction_deriv f a v θ hdiff, restriction_zero] at hEq
  simp only [zero_add, Nat.factorial_one, Nat.cast_one, div_one] at hEq
  linarith [hEq]

end MultivariateTaylor
