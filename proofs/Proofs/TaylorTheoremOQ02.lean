import Mathlib

/-!
# Analytic Functions and Taylor Series Convergence (OQ-02)

This file addresses the second open question from the Taylor's theorem gallery proof:
**For analytic functions, does the Taylor series converge to the function?**

For *smooth* functions, Taylor's theorem gives a remainder bound, but the remainder
can fail to vanish (Cauchy's example: f(x) = exp(-1/x²) at x=0 is C^∞ with all
derivatives 0, yet f(0) ≠ 0, so its Taylor series at 0 converges to 0 ≠ f).

For *analytic* functions—those with convergent power series—the Taylor series
always converges to the function in the ball of analyticity.

## Main Question (OQ-02)

> If f is analytic at x₀, does the Taylor remainder Rₙ(x) → 0 as n → ∞?

**Answer**: Yes, in the ball of analyticity. More precisely, if `HasFPowerSeriesOnBall f p x₀ r`
(f is known to agree with its power series `p` throughout the ball of radius `r` around x₀),
then for y with ‖y‖ < r:

  HasSum (fun n => (∂ⁿf/∂xⁿ)(x₀) / n! · yⁿ) (f (x₀ + y))

(Note: `r` here is the radius of the *known* representation, not `p.radius` — the abstract
radius of convergence of `p`'s coefficients. `p.radius` can strictly exceed `r`, since `f` need
not be analytic beyond the region it is actually known to agree with `p`'s sum.)

## Mathematical Structure

The proof connects two representations:
1. **Power series** (Mathlib): `HasSum (fun n => p n (fun _ => y)) (f (x₀+y))`
2. **Taylor series**: `HasSum (fun n => iteratedDeriv n f x₀ / n! · yⁿ) (f (x₀+y))`

The bridge: **p n (y,...,y) = (iteratedDeriv n f x₀) / n! · yⁿ**

This follows from:
- **Step 1 — Multilinearity**: `p n (y,...,y) = yⁿ · p n (1,...,1)` (trivial in 1D)
- **Step 2 — FPS-Derivative Bridge**: `n! · p n (1,...,1) = iteratedDeriv n f x₀`
  via `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum` + constant-vector simplification.

## Context

- **taylor-theorem** (Wiedijk #35): smooth functions, O(hⁿ) remainder *bound*.
- **taylor-theorem-oq-02** (this file): analytic functions, remainder *vanishes*.
- **taylor-theorem-oq-03**: exp convergence via ad hoc derivative bounds;
  this proof gives a structural explanation covering all analytic functions.

## References

- Mathlib `Analysis.Analytic.Basic`: `HasFPowerSeriesAt`, `HasFPowerSeriesOnBall`
- Mathlib `Analysis.Analytic.IteratedFDeriv`: `iteratedFDeriv_eq_sum`
- Mathlib `Analysis.Calculus.IteratedDeriv.Defs`: `iteratedDeriv` definition
-/

open Set Filter Topology Finset
open scoped Nat ENNReal NNNorm

namespace TaylorAnalytic

/-! ## Section 1: Multilinearity in 1D -/

/-- **Evaluating a 1D multilinear map at a constant vector**

For m : ℝⁿ → ℝ (continuous multilinear) and scalar y:
  m(y, y, ..., y) = yⁿ · m(1, 1, ..., 1)

Proof: `ContinuousMultilinearMap.map_smul_univ` gives
  m(c₁·v₁, ..., cₙ·vₙ) = (∏ cᵢ) · m(v₁,...,vₙ)
Setting cᵢ = y and vᵢ = 1: m(y,...,y) = (∏ᵢ y) · m(1,...,1) = yⁿ · m(1,...,1). -/
lemma multilinear_eval_const {n : ℕ}
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℝ) (y : ℝ) :
    m (fun _ => y) = y ^ n * m (fun _ => 1) := by
  have h := m.map_smul_univ (fun _ : Fin n => y) (fun _ => (1 : ℝ))
  simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ,
             Fintype.card_fin, smul_eq_mul] at h
  linarith

/-! ## Section 2: The FPS-Derivative Bridge -/

/-- **Key Bridge**: n-th power series coefficient at all-ones = iterated derivative / n!

  p n (1,...,1) = (∂ⁿf/∂xⁿ)(x₀) / n!

**Proof**: `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace` gives:
  iteratedFDeriv ℝ n f x₀ v = Σ_{σ ∈ Perm(Fin n)} p n (fun i => v (σ i))

For v = (1,...,1): v(σ i) = 1 for all σ, so each term equals p n (1,...,1).
The sum has n! terms, giving iteratedFDeriv ℝ n f x₀ (fun _ => 1) = n! · p n (1,...,1).
By definition, iteratedDeriv n f x₀ = iteratedFDeriv ℝ n f x₀ (fun _ => 1).
Dividing by n! yields the result. -/
lemma fps_coeff_eq_taylor_coeff {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x₀ : ℝ} (h : HasFPowerSeriesAt f p x₀) (n : ℕ) :
    p n (fun _ => (1 : ℝ)) = iteratedDeriv n f x₀ / (n ! : ℝ) := by
  obtain ⟨r, hr⟩ := h
  -- Step 1: Apply iteratedFDeriv_eq_sum_of_completeSpace (no global AnalyticOn needed)
  have key := hr.iteratedFDeriv_eq_sum_of_completeSpace (v := fun _ : Fin n => (1 : ℝ))
  -- Step 2: Simplify — (fun _ => 1)(σ i) = 1 for any permutation σ (constant function)
  -- key : iteratedFDeriv ℝ n f x₀ (fun _ => 1) = ∑ _ : Perm(Fin n), p n (fun _ => 1)
  -- Step 3: Sum of constant over Perm(Fin n) = n! copies
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at key
  -- key : iteratedFDeriv ℝ n f x₀ (fun _ => 1) = ↑(n !) * p n (fun _ => 1)
  -- Step 4: Rewrite iteratedDeriv using its definition = iteratedFDeriv (...) (fun _ => 1)
  rw [iteratedDeriv_eq_iteratedFDeriv, key]
  -- Goal: p n (fun _ => 1) = ↑(n !) * p n (fun _ => 1) / ↑(n !)
  have hn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hn]

/-- **FPS evaluation at y = Taylor polynomial term**

  p n (y,...,y) = (iteratedDeriv n f x₀ / n!) · yⁿ

This is the key bridge between `HasFPowerSeriesAt.hasSum` and the Taylor series. -/
lemma fps_eval_eq_taylor_term {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x₀ : ℝ} (h : HasFPowerSeriesAt f p x₀) (n : ℕ) (y : ℝ) :
    p n (fun _ => y) = iteratedDeriv n f x₀ / (n ! : ℝ) * y ^ n := by
  rw [multilinear_eval_const (p n) y, fps_coeff_eq_taylor_coeff h n]
  ring

/-! ## Section 3: Main Convergence Theorems -/

/-- **Taylor Series Convergence for Analytic Functions** (Main Result)

For f with a power series `p` known to converge to f throughout the ball of radius `r`
around x₀, the Taylor series converges:
  HasSum (fun n => (∂ⁿf/∂xⁿ)(x₀) / n! · yⁿ) (f (x₀ + y))
for all y with ‖y‖ < r.

**Proof**: `HasFPowerSeriesOnBall.hasSum` gives HasSum of `p n (fun _ => y)` to f(x₀ + y).
`fps_eval_eq_taylor_term` rewrites each term to the Taylor form.
`HasSum.congr_fun` completes the proof. -/
theorem taylor_hasSum_of_hasFPS {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x₀ : ℝ} {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p x₀ r) {y : ℝ}
    (hy : y ∈ Metric.eball (0 : ℝ) r) :
    HasSum (fun n => iteratedDeriv n f x₀ / (n ! : ℝ) * y ^ n) (f (x₀ + y)) :=
  (h.hasSum hy).congr_fun fun n => (fps_eval_eq_taylor_term h.hasFPowerSeriesAt n y).symm

/-- **Taylor Partial Sums Converge to f** -/
theorem taylor_tendsto_of_hasFPS {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x₀ : ℝ} {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p x₀ r) {y : ℝ}
    (hy : y ∈ Metric.eball (0 : ℝ) r) :
    Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, iteratedDeriv k f x₀ / (k ! : ℝ) * y ^ k)
      Filter.atTop (nhds (f (x₀ + y))) :=
  (taylor_hasSum_of_hasFPS h hy).tendsto_sum_nat

/-- **Taylor Remainder Vanishes for Analytic Functions** (OQ-02 Answer)

For f with power series `p` known to converge to f throughout the ball of radius `r`
around x₀, and y in that ball:
  f(x₀ + y) − Σ_{k<n} (∂ᵏf/∂xᵏ)(x₀) / k! · yᵏ → 0  as n → ∞

This answers OQ-02: for analytic functions, the Taylor remainder does not
merely stay bounded—it converges to zero throughout the region where the power
series is known to represent f. -/
theorem taylor_remainder_tendsto_zero {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x₀ : ℝ} {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p x₀ r) {y : ℝ}
    (hy : y ∈ Metric.eball (0 : ℝ) r) :
    Filter.Tendsto
      (fun n => f (x₀ + y) -
        ∑ k ∈ Finset.range n, iteratedDeriv k f x₀ / (k ! : ℝ) * y ^ k)
      Filter.atTop (nhds 0) := by
  have htend := taylor_tendsto_of_hasFPS h hy
  have hconst : Filter.Tendsto (fun _ : ℕ => f (x₀ + y)) Filter.atTop (nhds (f (x₀ + y))) :=
    tendsto_const_nhds
  simpa using hconst.sub htend

/-- **Tsum Form**: The Taylor series sum equals f

For analytic f, the infinite Taylor series converges to f:
  ∑' n, (∂ⁿf/∂xⁿ)(x₀) / n! · yⁿ = f(x₀ + y) -/
theorem taylor_tsum_eq {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x₀ : ℝ} {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p x₀ r) {y : ℝ}
    (hy : y ∈ Metric.eball (0 : ℝ) r) :
    ∑' n, iteratedDeriv n f x₀ / (n ! : ℝ) * y ^ n = f (x₀ + y) :=
  (taylor_hasSum_of_hasFPS h hy).tsum_eq

/-! ## Section 4: AnalyticAt Version -/

/-- **Existence of Taylor Convergence for Analytic Functions**

Every analytic function at x₀ has a power series p and a radius r > 0 such that
throughout the ball of radius r, the Taylor series of f converges to f(x₀ + y).

This is the main statement of OQ-02 from the gallery perspective. -/
theorem analyticAt_taylor_convergence {f : ℝ → ℝ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀) :
    ∃ (_p : FormalMultilinearSeries ℝ ℝ ℝ) (r : ℝ≥0∞), 0 < r ∧
      ∀ y : ℝ, y ∈ Metric.eball (0 : ℝ) r →
        HasSum (fun n => iteratedDeriv n f x₀ / (n ! : ℝ) * y ^ n) (f (x₀ + y)) := by
  obtain ⟨p, r, hr⟩ := hf
  exact ⟨p, r, hr.r_pos, fun y hy => taylor_hasSum_of_hasFPS hr hy⟩

/-- **Taylor Series as Tsum (AnalyticAt version)**

For f with power series `p` valid on the ball of radius `r` around x₀, the infinite
Taylor sum represents f throughout that ball. -/
theorem analyticAt_tsum_eq {f : ℝ → ℝ} {x₀ : ℝ}
    {p : FormalMultilinearSeries ℝ ℝ ℝ} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p x₀ r)
    {y : ℝ} (hy : y ∈ Metric.eball (0 : ℝ) r) :
    ∑' n, iteratedDeriv n f x₀ / (n ! : ℝ) * y ^ n = f (x₀ + y) :=
  taylor_tsum_eq hp hy

/-! ## Section 5: Concrete instances -/

/-- **Concrete instance**: fps_coeff_eq_taylor_coeff for n=1

For n=1, p 1 (fun _ => 1) equals f'(x₀) / 1! = f'(x₀).
This is the first derivative case of the general bridge. -/
example {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {x₀ : ℝ} (h : HasFPowerSeriesAt f p x₀) :
    p 1 (fun _ => (1 : ℝ)) = iteratedDeriv 1 f x₀ / (1 ! : ℝ) :=
  fps_coeff_eq_taylor_coeff h 1

/-! ## Verification -/

#check @multilinear_eval_const
#check @fps_coeff_eq_taylor_coeff
#check @fps_eval_eq_taylor_term
#check @taylor_hasSum_of_hasFPS
#check @taylor_tendsto_of_hasFPS
#check @taylor_remainder_tendsto_zero
#check @taylor_tsum_eq
#check @analyticAt_taylor_convergence

end TaylorAnalytic
