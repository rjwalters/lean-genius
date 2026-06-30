import Proofs.MeanValueTheoremOQ02
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Mean Value Theorem OQ-02-OQ-01: Taylor remainder *estimates* and series convergence

## The open question (from `mean-value-theorem-oq-02`)

The parent entry proved Taylor's theorem with the **Lagrange remainder** as an exact
equality (`MeanValueTheoremOQ02.taylor_lagrange_remainder`):

  f(b) - Tₙ(b) = f⁽ⁿ⁺¹⁾(c)/(n+1)! · (b-a)ⁿ⁺¹   for some c ∈ (a,b).

The open follow-up asks: how does this exact remainder turn **derivative control into
function-value control**, and how does it drive the convergence of the Taylor *series*?
That is the bridge `whyMatters` highlights ("Taylor remainder estimates depend on
converting derivative control into function-value control").

## What this file proves (all from the parent's exact Lagrange remainder)

* `taylor_remainder_bound` — if `|f⁽ⁿ⁺¹⁾| ≤ M` on `(a,b)` then
    `|f(b) - Tₙ(b)| ≤ M/(n+1)! · (b-a)ⁿ⁺¹`.
  This is the sharp `(n+1)!` estimate (sharper than Mathlib's
  `taylor_mean_remainder_bound`, which carries the weaker `n!`), obtained directly by
  taking absolute values in the Lagrange equality.

* `taylorPolynomial_tendsto` — if **all** derivatives of `f` are uniformly bounded by a
  single constant `M` on `(a,b)`, then `Tₙ(b) → f(b)`, i.e. the Taylor series of `f`
  centered at `a` converges to `f(b)`.  The engine is `(b-a)ⁿ⁺¹/(n+1)! → 0`.

* `iteratedDeriv_exp`, `taylorPolynomial_exp` — the iterated derivatives of `exp` are
  `exp`, so its Taylor polynomial at `0` is the partial exponential sum `∑ xᵏ/k!`.

* `exp_taylor_tendsto` — the headline concrete payoff: for `x > 0`,
    `∑_{k≤n} xᵏ/k! → exp x`,
  derived purely from the remainder estimate (every derivative of `exp` on `(0,x)` is
  bounded by `exp x`).

## Honesty / scope

The Lagrange remainder itself comes from Mathlib via the parent file; this file's
contribution is the *estimate* layer (derivative bound ⇒ value bound ⇒ series
convergence) and its application to `exp`.  Mathlib of course already knows the
exponential series converges; the point here is that it falls out of the MVT/Taylor
remainder machinery rather than from the power-series definition.

Theorems: 5, Axioms: 0, Sorries: 0
-/

noncomputable section

open Real Set Filter Topology MeanValueTheoremOQ02

namespace MeanValueTheoremOQ02OQ01

/-!
## Part I: The Taylor remainder estimate

Taking absolute values in the parent's exact Lagrange remainder converts a bound on the
`(n+1)`-th derivative into a bound on the approximation error.
-/

/-- **Taylor remainder estimate (sharp constant).**

If `f` is `(n+1)`-times continuously differentiable and its `(n+1)`-th derivative is
bounded in absolute value by `M` on `(a,b)`, then the `n`-th Taylor polynomial
approximates `f(b)` with error at most `M/(n+1)! · (b-a)ⁿ⁺¹`.

This is the direct payoff of the Lagrange remainder: derivative control becomes
function-value control. -/
theorem taylor_remainder_bound
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (n : ℕ) (M : ℝ)
    (hf : ContDiff ℝ (n + 1) f)
    (hM : ∀ x ∈ Set.Ioo a b, |iteratedDeriv (n + 1) f x| ≤ M) :
    |f b - taylorPolynomial f a n b| ≤
      M / ((n + 1).factorial : ℝ) * (b - a) ^ (n + 1) := by
  obtain ⟨c, hc, heq⟩ := taylor_lagrange_remainder f a b hab n hf
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
    exact_mod_cast (n + 1).factorial_pos
  have hba : (0 : ℝ) < (b - a) ^ (n + 1) := pow_pos (sub_pos.mpr hab) _
  rw [heq, abs_mul, abs_div, abs_of_pos hfac, abs_of_pos hba]
  gcongr
  exact hM c hc

/-!
## Part II: Convergence of the Taylor series

If a single constant `M` bounds *every* derivative of `f` on `(a,b)`, the remainder
estimate forces `Tₙ(b) → f(b)`, because `(b-a)ⁿ⁺¹/(n+1)! → 0`.
-/

/-- **Convergence of the Taylor series from a uniform derivative bound.**

If `f` is smooth and there is a single constant `M` bounding the absolute value of
*all* of its derivatives on `(a,b)`, then its Taylor polynomials at `a` converge to
`f(b)`. Functions like `sin`, `cos`, and `exp` (on a bounded interval) satisfy this. -/
theorem taylorPolynomial_tendsto
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (M : ℝ)
    (hf : ContDiff ℝ ⊤ f)
    (hM : ∀ n : ℕ, ∀ x ∈ Set.Ioo a b, |iteratedDeriv n f x| ≤ M) :
    Tendsto (fun n => taylorPolynomial f a n b) atTop (𝓝 (f b)) := by
  -- The error bound `g n = M · (b-a)ⁿ⁺¹/(n+1)!`.
  set g : ℕ → ℝ := fun n => M * ((b - a) ^ (n + 1) / ((n + 1).factorial : ℝ)) with hg_def
  -- The remainder estimate applied at each `n`.
  have hbnd : ∀ n, |taylorPolynomial f a n b - f b| ≤ g n := by
    intro n
    have h := taylor_remainder_bound f a b hab n M (hf.of_le le_top)
      (fun x hx => hM (n + 1) x hx)
    rw [abs_sub_comm]
    refine h.trans_eq ?_
    rw [hg_def]; ring
  -- The error bound tends to `0` (terms of the convergent series `M·∑ (b-a)ᵏ/k!`).
  have hg : Tendsto g atTop (𝓝 0) := by
    have hs : Summable (fun k : ℕ => M * ((b - a) ^ k / (k.factorial : ℝ))) :=
      (Real.summable_pow_div_factorial (b - a)).mul_left M
    have h0 := hs.tendsto_atTop_zero
    exact h0.comp (tendsto_add_atTop_nat 1)
  -- Squeeze: the (signed) error tends to `0`, hence `Tₙ(b) → f(b)`.
  have hF : Tendsto (fun n => taylorPolynomial f a n b - f b) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hg
    simpa [Real.norm_eq_abs] using hbnd n
  have := hF.add (tendsto_const_nhds (x := f b))
  simpa using this

/-!
## Part III: The exponential function

The iterated derivatives of `exp` are all `exp`, so its Taylor polynomial at `0` is the
familiar partial sum `∑ xᵏ/k!`, and the remainder machinery yields convergence.
-/

/-- Every iterated derivative of `Real.exp` is `Real.exp` itself. -/
theorem iteratedDeriv_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  rw [iteratedDeriv_eq_iterate]
  exact Real.iter_deriv_exp n

/-- The `n`-th Taylor polynomial of `exp` centered at `0` is the partial exponential
sum `∑_{k≤n} xᵏ/k!`. -/
theorem taylorPolynomial_exp (n : ℕ) (x : ℝ) :
    taylorPolynomial Real.exp 0 n x =
      ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ) := by
  simp only [taylorPolynomial, iteratedDeriv_exp, Real.exp_zero, sub_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Convergence of the exponential Taylor series**, derived from the Taylor remainder
estimate.

For `x > 0`, the partial sums `∑_{k≤n} xᵏ/k!` converge to `exp x`. The key bound is that
every derivative of `exp` on `(0,x)` is at most `exp x`, so the uniform-bound
convergence result applies. -/
theorem exp_taylor_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ))
      atTop (𝓝 (Real.exp x)) := by
  have hM : ∀ n : ℕ, ∀ y ∈ Set.Ioo (0 : ℝ) x, |iteratedDeriv n Real.exp y| ≤ Real.exp x := by
    intro n y hy
    rw [iteratedDeriv_exp, abs_of_pos (Real.exp_pos y)]
    exact Real.exp_le_exp.mpr (le_of_lt hy.2)
  have key := taylorPolynomial_tendsto Real.exp 0 x hx (Real.exp x) Real.contDiff_exp hM
  exact key.congr (fun n => taylorPolynomial_exp n x)

end MeanValueTheoremOQ02OQ01
