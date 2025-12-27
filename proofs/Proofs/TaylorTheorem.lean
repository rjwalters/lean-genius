import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

/-!
# Taylor's Theorem

## What This Proves
Taylor's Theorem gives a polynomial approximation to a sufficiently differentiable
function near a point, along with an explicit remainder term. If f is n+1 times
differentiable on an interval containing a and x, then:

**Taylor Expansion**:
  f(x) = f(a) + f'(a)(x-a) + f''(a)(x-a)²/2! + ... + f⁽ⁿ⁾(a)(x-a)ⁿ/n! + Rₙ(x)

The remainder Rₙ(x) can be expressed in several forms:

**Lagrange Form**: Rₙ(x) = f⁽ⁿ⁺¹⁾(ξ)(x-a)ⁿ⁺¹/(n+1)! for some ξ between a and x

**Cauchy Form**: Rₙ(x) = f⁽ⁿ⁺¹⁾(ξ)(x-ξ)ⁿ(x-a)/(n!) for some ξ between a and x

## Wiedijk 100 Theorems: #35
This is entry #35 in Freek Wiedijk's list of 100 famous theorems.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `taylor_mean_remainder_lagrange`
  and `taylor_mean_remainder_cauchy` theorems from `Analysis.Calculus.Taylor`.
- **Key Insight:** The Taylor polynomial provides the best polynomial approximation
  of degree n to a smooth function at a point. The remainder term quantifies the error.
- **Proof Techniques Demonstrated:** Working with iterated derivatives, factorial
  denominators, and mean value theorem applications.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples

## Mathlib Dependencies
- `taylorWithinEval` : Taylor polynomial evaluation
- `taylor_mean_remainder_lagrange` : Lagrange form of remainder
- `taylor_mean_remainder_cauchy` : Cauchy form of remainder
- `taylor_mean_remainder_bound` : Bound on remainder term

## Historical Note
Taylor's theorem is named after Brook Taylor, who published a version in 1715.
However, the result was known earlier to James Gregory (1671) and others.
Colin Maclaurin published the special case with a = 0 (now called Maclaurin series)
in 1742. The rigorous formulation with remainder terms was developed by
Lagrange (1797), Cauchy, and later analysts. The theorem is fundamental to
numerical analysis, optimization, and the theory of analytic functions.
-/

open Set Filter Topology Finset
open scoped Nat

namespace TaylorTheorem

/-! ## Taylor Polynomial

The Taylor polynomial of degree n at point x₀ approximates f by matching
its first n derivatives at x₀. -/

/-- **Taylor Polynomial (Wiedijk #35)**

The Taylor polynomial of degree n for f at x₀ is:
  T_n(x) = Σ_{k=0}^{n} f⁽ᵏ⁾(x₀) · (x - x₀)ᵏ / k!

This is Mathlib's `taylorWithinEval` function. -/
noncomputable def taylorPoly (f : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ) : ℝ :=
  taylorWithinEval f n (Icc x₀ x) x₀ x

/-! ## Lagrange Remainder Form

The most commonly used form of the remainder. -/

/-- **Taylor's Theorem with Lagrange Remainder (Wiedijk #35)**

For a function f that is (n+1)-times continuously differentiable on [x₀, x]:

  f(x) = T_n(x) + f⁽ⁿ⁺¹⁾(x') · (x - x₀)ⁿ⁺¹ / (n+1)!

for some x' ∈ (x₀, x).

This is the Lagrange form, which expresses the error in terms of the (n+1)-th
derivative at an intermediate point. -/
theorem taylor_lagrange {f : ℝ → ℝ} {x₀ x : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ (n + 1) f (Icc x₀ x)) :
    ∃ x' ∈ Ioo x₀ x,
      f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
        iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have hf_n : ContDiffOn ℝ n f (Icc x₀ x) := hf.of_succ
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x) := by
    have hlt : (n : ℕ∞) < n + 1 := by norm_cast; omega
    have h := hf.differentiableOn_iteratedDerivWithin (m := n) hlt (uniqueDiffOn_Icc hx)
    exact h.mono Ioo_subset_Icc_self
  exact taylor_mean_remainder_lagrange hx hf_n hdiff

/-! ## Cauchy Remainder Form

An alternative form of the remainder, sometimes more convenient for estimation. -/

/-- **Taylor's Theorem with Cauchy Remainder**

For a function f that is (n+1)-times continuously differentiable on [x₀, x]:

  f(x) = T_n(x) + f⁽ⁿ⁺¹⁾(x') · (x - x')ⁿ · (x - x₀) / n!

for some x' ∈ (x₀, x).

The Cauchy form is useful when estimating integrals of the remainder. -/
theorem taylor_cauchy {f : ℝ → ℝ} {x₀ x : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ (n + 1) f (Icc x₀ x)) :
    ∃ x' ∈ Ioo x₀ x,
      f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
        iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) := by
  have hf_n : ContDiffOn ℝ n f (Icc x₀ x) := hf.of_succ
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x) := by
    have hlt : (n : ℕ∞) < n + 1 := by norm_cast; omega
    have h := hf.differentiableOn_iteratedDerivWithin (m := n) hlt (uniqueDiffOn_Icc hx)
    exact h.mono Ioo_subset_Icc_self
  exact taylor_mean_remainder_cauchy hx hf_n hdiff

/-! ## Remainder Bounds

When we know a bound on the (n+1)-th derivative, we can bound the remainder. -/

/-- **Taylor Remainder Bound**

If |f⁽ⁿ⁺¹⁾| ≤ C on [a, b], then the Taylor remainder satisfies:

  |f(x) - T_n(x)| ≤ C · (x - a)ⁿ⁺¹ / n!

This bound is essential for convergence analysis. -/
theorem taylor_remainder_bound {f : ℝ → ℝ} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n ! :=
  taylor_mean_remainder_bound hab hf hx hC

/-! ## First-Order Taylor: Mean Value Theorem

The n=0 case reduces to the Mean Value Theorem. -/

/-- **First-Order Taylor (Mean Value Theorem)**

When n = 0, Taylor's theorem gives:
  f(x) = f(x₀) + f'(x') · (x - x₀)

for some x' ∈ (x₀, x). This is the Mean Value Theorem. -/
theorem taylor_first_order {f : ℝ → ℝ} {x₀ x : ℝ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ 1 f (Icc x₀ x)) :
    ∃ x' ∈ Ioo x₀ x,
      f x - f x₀ = iteratedDerivWithin 1 f (Icc x₀ x) x' * (x - x₀) := by
  have h := taylor_lagrange (n := 0) hx hf
  obtain ⟨x', hx'_mem, hx'_eq⟩ := h
  use x', hx'_mem
  simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hx'_eq
  simp only [taylor_within_zero_eval] at hx'_eq
  exact hx'_eq

/-! ## Second-Order Taylor

The n=1 case gives the familiar quadratic approximation. -/

/-- **Second-Order Taylor**

When n = 1, Taylor's theorem gives the quadratic approximation:
  f(x) = f(x₀) + f'(x₀)(x - x₀) + f''(x')(x - x₀)²/2

for some x' ∈ (x₀, x). -/
theorem taylor_second_order {f : ℝ → ℝ} {x₀ x : ℝ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ 2 f (Icc x₀ x)) :
    ∃ x' ∈ Ioo x₀ x,
      f x - taylorWithinEval f 1 (Icc x₀ x) x₀ x =
        iteratedDerivWithin 2 f (Icc x₀ x) x' * (x - x₀) ^ 2 / 2 := by
  have h := taylor_lagrange (n := 1) hx hf
  simp only [Nat.factorial_two, Nat.cast_ofNat] at h
  exact h

/-! ## Existence of Remainder Bound

For any smooth function on a closed interval, there exists a uniform bound. -/

/-- **Existence of Taylor Remainder Bound**

For any (n+1)-times continuously differentiable function on [a, b], there exists
a constant C such that the remainder is bounded by C · (x - a)^(n+1). -/
theorem exists_taylor_remainder_bound {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) :=
  exists_taylor_mean_remainder_bound hab hf

/-! ## Verification -/

#check taylor_lagrange
#check taylor_cauchy
#check taylor_remainder_bound
#check taylor_first_order
#check taylor_second_order
#check exists_taylor_remainder_bound

end TaylorTheorem
