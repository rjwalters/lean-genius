/-
# Mean Value Theorem OQ-02-OQ-01-OQ-02: Global convergence of the Taylor series of `sin` and `cos`

**Open question (parent `MeanValueTheoremOQ02OQ01`).** The parent file distilled Taylor's
exact Lagrange remainder into a reusable convergence engine:

> `taylorPolynomial_tendsto` — if a *single* constant `M` bounds **every** iterated
> derivative `|f⁽ⁿ⁾|` on an interval `(a,b)`, then the Taylor partial sums `Tₙ(b)`
> converge to `f(b)`.

The parent's headline payoff was the exponential series, but only for `x > 0`: `exp` has
no uniform global derivative bound, so its convergence argument is intrinsically
one-sided.

`sin` and `cos` are the opposite extreme. Their derivatives cycle through
`±sin, ±cos`, every one bounded by the **single global constant `M = 1`**
(`Real.abs_iteratedDeriv_sin_le_one`, `Real.abs_iteratedDeriv_cos_le_one`). This file
turns that global bound into **global convergence**:

> For every `x : ℝ`, `Tₙ(x) → sin x` and `Tₙ(x) → cos x`,

with the Taylor polynomials centred at `0`. The positive half-line is the parent engine
applied with `M = 1`. The negative half-line is *not* a second analytic argument: it is
recovered from the positive one by the parity of `sin` (odd) and `cos` (even), encoded in
the termwise reflection identities `Tₙ(sin, -x) = -Tₙ(sin, x)` and
`Tₙ(cos, -x) = Tₙ(cos, x)`. The vanishing of the "wrong-parity" Taylor coefficients
(`iteratedDeriv (2m) sin 0 = 0`, `iteratedDeriv (2m+1) cos 0 = 0`) is exactly what makes
these reflections hold.

## What is new

Mathlib records the *power-series* convergence of `sin`/`cos` (`Real.hasSum_sin`,
`Real.hasSum_cos`), proved from the complex exponential. The result here is the same
analytic fact obtained instead from the **mean-value / Taylor-remainder route** of the
parent thread, and phrased for the parent's concrete `taylorPolynomial` object on **all of
ℝ** — the genuine strengthening over the parent's one-sided exponential result, powered by
the global nature of the bound `M = 1`.

## Results

1. `sin_taylor_tendsto_pos`, `cos_taylor_tendsto_pos` — the engine on `x > 0`.
2. `taylorPolynomial_sin_neg`, `taylorPolynomial_cos_neg` — the parity reflections.
3. `sin_taylor_tendsto`, `cos_taylor_tendsto` — convergence on **all of ℝ**.

## Axioms: 0 | Sorries: 0
-/
import Mathlib
import Proofs.MeanValueTheoremOQ02
import Proofs.MeanValueTheoremOQ02OQ01

namespace MeanValueTheoremOQ02OQ01OQ02

open Real Set Filter Topology MeanValueTheoremOQ02 MeanValueTheoremOQ02OQ01

/-! ## Part I: The positive half-line, from the parent engine -/

/-- **Convergence of the `sin` Taylor series for `x > 0`.** Every iterated derivative of
`sin` is bounded by the single global constant `1`, so the parent's uniform-bound engine
`taylorPolynomial_tendsto` applies directly with `M = 1`. -/
theorem sin_taylor_tendsto_pos {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => taylorPolynomial Real.sin 0 n x) atTop (𝓝 (Real.sin x)) :=
  taylorPolynomial_tendsto Real.sin 0 x hx 1 Real.contDiff_sin
    (fun n y _ => Real.abs_iteratedDeriv_sin_le_one n y)

/-- **Convergence of the `cos` Taylor series for `x > 0`.** Same global bound `M = 1`. -/
theorem cos_taylor_tendsto_pos {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n => taylorPolynomial Real.cos 0 n x) atTop (𝓝 (Real.cos x)) :=
  taylorPolynomial_tendsto Real.cos 0 x hx 1 Real.contDiff_cos
    (fun n y _ => Real.abs_iteratedDeriv_cos_le_one n y)

/-! ## Part II: Parity reflections of the Taylor polynomials at `0` -/

/-- **Odd reflection for `sin`.** Because the even-order Taylor coefficients of `sin` at
`0` vanish (`iteratedDeriv (2m) sin 0 = (-1)ᵐ · sin 0 = 0`), the Taylor polynomial of `sin`
is an odd function of its argument: `Tₙ(sin, -x) = -Tₙ(sin, x)`. -/
theorem taylorPolynomial_sin_neg (n : ℕ) (x : ℝ) :
    taylorPolynomial Real.sin 0 n (-x) = - taylorPolynomial Real.sin 0 n x := by
  simp only [taylorPolynomial, sub_zero]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- even order: the coefficient is zero
    have hd : iteratedDeriv (m + m) Real.sin 0 = 0 := by
      have h := congrFun (Real.iteratedDeriv_even_sin m) 0
      rw [show 2 * m = m + m by ring] at h
      simpa [Real.sin_zero] using h
    rw [hd]; ring
  · -- odd order: an odd power flips sign
    rw [Odd.neg_pow ⟨m, rfl⟩ x]; ring

/-- **Even reflection for `cos`.** Because the odd-order Taylor coefficients of `cos` at
`0` vanish (`iteratedDeriv (2m+1) cos 0 = (-1)^{m+1} · sin 0 = 0`), the Taylor polynomial of
`cos` is an even function of its argument: `Tₙ(cos, -x) = Tₙ(cos, x)`. -/
theorem taylorPolynomial_cos_neg (n : ℕ) (x : ℝ) :
    taylorPolynomial Real.cos 0 n (-x) = taylorPolynomial Real.cos 0 n x := by
  simp only [taylorPolynomial, sub_zero]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- even order: an even power is unchanged
    rw [Even.neg_pow ⟨m, rfl⟩ x]
  · -- odd order: the coefficient is zero
    have hd : iteratedDeriv (2 * m + 1) Real.cos 0 = 0 := by
      have h := congrFun (Real.iteratedDeriv_odd_cos m) 0
      simpa [Real.sin_zero] using h
    rw [hd]; ring

/-! ## Part III: Convergence on all of ℝ -/

/-- The Taylor polynomial centred at `0`, evaluated at the centre, is the constant `f 0`. -/
private theorem taylorPolynomial_at_zero (f : ℝ → ℝ) (n : ℕ) :
    taylorPolynomial f 0 n 0 = f 0 := by
  simp only [taylorPolynomial, sub_zero]
  rw [Finset.sum_eq_single 0]
  · simp [iteratedDeriv_zero]
  · intro k _ hk; simp [zero_pow hk]
  · intro h; simp at h

/-- **Global convergence of the `sin` Taylor series.** For *every* `x : ℝ`, the Taylor
partial sums centred at `0` converge to `sin x`. The case `x > 0` is the parent engine; the
centre `x = 0` is constant; and `x < 0` is reduced to `-x > 0` through the odd reflection
`taylorPolynomial_sin_neg`, using `sin (-x) = -sin x`. -/
theorem sin_taylor_tendsto (x : ℝ) :
    Tendsto (fun n => taylorPolynomial Real.sin 0 n x) atTop (𝓝 (Real.sin x)) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- x < 0
    have hpos : 0 < -x := by linarith
    have key := (sin_taylor_tendsto_pos hpos).neg
    rw [Real.sin_neg, neg_neg] at key
    refine key.congr (fun n => ?_)
    rw [taylorPolynomial_sin_neg, neg_neg]
  · -- x = 0
    subst hx
    have hc : Tendsto (fun _ : ℕ => Real.sin 0) atTop (𝓝 (Real.sin 0)) := tendsto_const_nhds
    exact hc.congr (fun n => (taylorPolynomial_at_zero Real.sin n).symm)
  · -- x > 0
    exact sin_taylor_tendsto_pos hx

/-- **Global convergence of the `cos` Taylor series.** For *every* `x : ℝ`, the Taylor
partial sums centred at `0` converge to `cos x`. Here the negative half-line is reduced to
`-x > 0` through the *even* reflection `taylorPolynomial_cos_neg` and `cos (-x) = cos x`. -/
theorem cos_taylor_tendsto (x : ℝ) :
    Tendsto (fun n => taylorPolynomial Real.cos 0 n x) atTop (𝓝 (Real.cos x)) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- x < 0
    have hpos : 0 < -x := by linarith
    have key := cos_taylor_tendsto_pos hpos
    rw [Real.cos_neg] at key
    refine key.congr (fun n => ?_)
    rw [taylorPolynomial_cos_neg]
  · -- x = 0
    subst hx
    have hc : Tendsto (fun _ : ℕ => Real.cos 0) atTop (𝓝 (Real.cos 0)) := tendsto_const_nhds
    exact hc.congr (fun n => (taylorPolynomial_at_zero Real.cos n).symm)
  · -- x > 0
    exact cos_taylor_tendsto_pos hx

/-! ## Spot checks -/

/-- The reflection is a genuine sign flip at, e.g., `n = 3`: the cubic Taylor polynomial of
`sin` is odd. -/
example (x : ℝ) :
    taylorPolynomial Real.sin 0 3 (-x) = - taylorPolynomial Real.sin 0 3 x :=
  taylorPolynomial_sin_neg 3 x

/-- Convergence holds at a concrete negative point, exercising the reflection branch. -/
example : Tendsto (fun n => taylorPolynomial Real.sin 0 n (-1)) atTop (𝓝 (Real.sin (-1))) :=
  sin_taylor_tendsto (-1)

end MeanValueTheoremOQ02OQ01OQ02
