import Proofs.MeanValueTheoremOQ02OQ01
import Mathlib.Tactic

/-!
# Mean Value Theorem OQ-02-OQ-01-OQ-01: exp Taylor convergence for *all* real x

## The open question (from `mean-value-theorem-oq-02-oq-01`)

The parent entry proved `exp_taylor_tendsto`: for `x > 0`, the partial sums
`∑_{k≤n} xᵏ/k!` converge to `exp x`, derived purely from the Lagrange/Taylor
remainder estimate (every derivative of `exp` on `(0,x)` is bounded by `exp x`).

The remainder machinery as stated there is one-sided: it needs an interval `(a,b)`
with `a < b`, so it only reaches `x > 0`. The follow-up asks: **does the same
remainder argument deliver convergence for all real `x`, including `x ≤ 0`?**

## What this file proves

* `iteratedDeriv_exp_neg` — the iterated derivatives of `t ↦ exp(-t)` are
  `t ↦ (-1)ⁿ exp(-t)`.
* `exp_taylor_tendsto_neg` — for `x < 0`, `∑_{k≤n} xᵏ/k! → exp x`.
  This is the genuinely new direction. Rather than re-deriving a leftward Taylor
  remainder, we **reflect**: apply the parent's `taylorPolynomial_tendsto` to the
  function `t ↦ exp(-t)` on the positive interval `(0, -x)`. Its derivatives are all
  bounded by `1` there, its Taylor polynomial at `0` is exactly `∑_{k≤n} xᵏ/k!`
  (because `(-(-x))ᵏ = xᵏ`), and its value at `-x` is `exp x`.
* `exp_taylor_tendsto_all` — the headline: for **every** real `x`,
  `∑_{k≤n} xᵏ/k! → exp x`. Trichotomy glues the negative case, the trivial `x = 0`
  case (partial sums are constantly `1 = exp 0`), and the parent's positive case.

## Honesty / scope

The negative case still comes from the Mean-Value/Taylor remainder estimate — the
reflection `t ↦ exp(-t)` is exactly what lets the one-sided parent lemma cover the
left half-line, so the entry stays in the "remainder machinery, not power-series
definition" spirit of its parent. Mathlib already knows the exponential series
converges everywhere (`Real.summable_pow_div_factorial`); the contribution here is the
two-sided convergence falling out of the MVT remainder bound.

Theorems: 4, Axioms: 0, Sorries: 0
-/

noncomputable section

open Real Set Filter Topology MeanValueTheoremOQ02 MeanValueTheoremOQ02OQ01

namespace MeanValueTheoremOQ02OQ01OQ01

/-!
## Part I: Derivatives of the reflected exponential

Every iterated derivative of `t ↦ exp(-t)` is `t ↦ (-1)ⁿ exp(-t)`. This is the input
needed to identify the Taylor polynomial of the reflection and to bound its
derivatives.
-/

/-- The first derivative of `t ↦ exp(-t)` is `t ↦ -exp(-t)`. -/
theorem deriv_exp_neg (x : ℝ) :
    deriv (fun t => Real.exp (-t)) x = -Real.exp (-x) := by
  have h : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-x)) x := by
    have h1 : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
    have h2 := (Real.hasDerivAt_exp (-x)).comp x h1
    simpa using h2
  exact h.deriv

/-- **Iterated derivatives of the reflected exponential.**
`iteratedDeriv n (t ↦ exp(-t)) = t ↦ (-1)ⁿ exp(-t)`. -/
theorem iteratedDeriv_exp_neg (n : ℕ) :
    iteratedDeriv n (fun t => Real.exp (-t)) = fun t => (-1) ^ n * Real.exp (-t) := by
  induction n with
  | zero => funext t; simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hdiff : DifferentiableAt ℝ (fun t => Real.exp (-t)) t := by fun_prop
    rw [deriv_const_mul _ hdiff, deriv_exp_neg]
    ring

/-!
## Part II: Convergence for negative arguments (the new direction)

For `x < 0`, set `y = -x > 0` and apply the parent's `taylorPolynomial_tendsto` to the
reflection `f t = exp(-t)` on `(0, y)`. Its derivatives are bounded there by `1`, so its
Taylor polynomials at `0` converge to `f y = exp(-y) = exp x`; and those Taylor
polynomials are exactly `∑_{k≤n} xᵏ/k!`.
-/

/-- **Exponential Taylor series converges for negative arguments.**
For `x < 0`, `∑_{k≤n} xᵏ/k! → exp x`, via the parent's remainder estimate applied to the
reflected exponential. -/
theorem exp_taylor_tendsto_neg {x : ℝ} (hx : x < 0) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ))
      atTop (𝓝 (Real.exp x)) := by
  set y := -x with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hxy : x = -y := by rw [hy]; ring
  -- All iterated derivatives of `t ↦ exp(-t)` are bounded by `1` on `(0, y)`.
  have hM : ∀ n : ℕ, ∀ t ∈ Set.Ioo (0 : ℝ) y,
      |iteratedDeriv n (fun s => Real.exp (-s)) t| ≤ 1 := by
    intro n t ht
    rw [iteratedDeriv_exp_neg]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-t) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith [ht.1])
      _ = 1 := Real.exp_zero
  have hcontdiff : ContDiff ℝ ⊤ (fun s => Real.exp (-s)) := by fun_prop
  have key := taylorPolynomial_tendsto (fun s => Real.exp (-s)) 0 y hy0 1 hcontdiff hM
  -- The limit `f y = exp(-y) = exp x`.
  have hfy : (fun s => Real.exp (-s)) y = Real.exp x := by rw [hxy]
  rw [hfy] at key
  -- The Taylor polynomial of the reflection at `0` is exactly `∑ xᵏ/k!`.
  refine key.congr ?_
  intro n
  rw [taylorPolynomial]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : iteratedDeriv k (fun s => Real.exp (-s)) 0 = (-1) ^ k := by
    rw [iteratedDeriv_exp_neg]; simp
  have h2 : x ^ k = (-1) ^ k * y ^ k := by rw [hxy, neg_pow]
  rw [h1, h2, sub_zero]
  ring

/-!
## Part III: The headline — convergence for all real x
-/

/-- **Exponential Taylor series converges for every real argument.**
For all `x : ℝ`, the partial sums `∑_{k≤n} xᵏ/k!` converge to `exp x`. The three cases
`x < 0`, `x = 0`, `x > 0` come respectively from the reflection argument above, a
constant-sequence computation, and the parent's `exp_taylor_tendsto`. -/
theorem exp_taylor_tendsto_all (x : ℝ) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ))
      atTop (𝓝 (Real.exp x)) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact exp_taylor_tendsto_neg hx
  · subst hx
    -- At `x = 0` only the `k = 0` term survives: every partial sum equals `1 = exp 0`.
    have hconst : ∀ n : ℕ,
        (∑ k ∈ Finset.range (n + 1), (0 : ℝ) ^ k / (k.factorial : ℝ)) = 1 := by
      intro n
      rw [Finset.sum_eq_single 0
        (fun b _ hb => by rw [zero_pow hb]; simp)
        (fun h => absurd (Finset.mem_range.mpr n.succ_pos) h)]
      simp
    rw [Real.exp_zero]
    exact tendsto_const_nhds.congr (fun n => (hconst n).symm)
  · exact exp_taylor_tendsto hx

end MeanValueTheoremOQ02OQ01OQ01
