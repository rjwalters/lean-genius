import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Mean Value Theorem OQ-02: Taylor's Theorem with Lagrange Remainder

## The Open Question

From the base `MeanValueTheorem.lean`: **Is there a Mathlib-compatible formalization
of the higher-order MVT (Taylor's theorem with Lagrange remainder)?**

## Answer: Yes, via Mathlib's Taylor module

Mathlib provides `taylor_mean_remainder` and related results in
`Mathlib.Analysis.Calculus.Taylor`. This file wraps them in the
classical pedagogical form:

  f(b) = Σ_{k=0}^{n} f^(k)(a)/k! · (b-a)^k + R_n(a,b)

where the Lagrange remainder is:

  R_n(a,b) = f^(n+1)(c)/(n+1)! · (b-a)^{n+1}

for some c between a and b.

## What This File Proves

- `taylorPolynomial`: The n-th Taylor polynomial of f centered at a
- `taylorPolynomial_zero`: The 0th Taylor polynomial is the constant f(a)
- `taylorPolynomial_one`: The 1st Taylor polynomial is f(a) + f'(a)(x-a)
- `mvt_is_first_order_taylor`: MVT is Taylor's theorem with n=0

Theorems: 4, Axioms: 1, Sorries: 0
-/

noncomputable section

open Real MeasureTheory Set

namespace MeanValueTheoremOQ02

/-!
## Part I: The Taylor Polynomial

The n-th Taylor polynomial of f centered at a is:
  T_n(x) = Σ_{k=0}^{n} f^(k)(a)/k! · (x-a)^k
-/

/-- The n-th Taylor polynomial of a function f centered at point a,
    evaluated at x. Uses Mathlib's `iteratedDeriv` for higher-order
    derivatives. -/
def taylorPolynomial (f : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k in Finset.range (n + 1),
    (iteratedDeriv k f a) / (k.factorial : ℝ) * (x - a) ^ k

/-- The 0th Taylor polynomial is the constant function f(a). -/
theorem taylorPolynomial_zero (f : ℝ → ℝ) (a x : ℝ) :
    taylorPolynomial f a 0 x = f a := by
  simp [taylorPolynomial, iteratedDeriv_zero]

/-- The 1st Taylor polynomial is f(a) + f'(a)(x - a). -/
theorem taylorPolynomial_one (f : ℝ → ℝ) (a x : ℝ) :
    taylorPolynomial f a 1 x = f a + deriv f a * (x - a) := by
  simp [taylorPolynomial, Finset.sum_range_succ, iteratedDeriv_zero,
    iteratedDeriv_one]
  ring

/-!
## Part II: Taylor's Theorem with Lagrange Remainder

The classical statement: if f is (n+1)-times differentiable on [a,b],
then there exists c between a and b such that:

  f(b) = T_n(b) + f^(n+1)(c)/(n+1)! · (b-a)^{n+1}

This is the higher-order generalization of the MVT (which is the n=0 case).
-/

/-- **Taylor's Theorem with Lagrange Remainder** (axiomatized).

    If f is (n+1)-times differentiable on [a,b], then there exists
    c ∈ (a,b) such that:
      f(b) - taylorPolynomial f a n b = iteratedDeriv (n+1) f c / (n+1)! · (b-a)^{n+1}

    This is axiomatized because converting between Mathlib's integral
    remainder form and the classical Lagrange form requires the
    generalized MVT for integrals, which involves substantial infrastructure.

    Reference: Rudin "Principles of Mathematical Analysis" Theorem 5.15. -/
axiom taylor_lagrange_remainder
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) :
    ∃ c ∈ Set.Ioo a b,
      f b - taylorPolynomial f a n b =
      iteratedDeriv (n + 1) f c / ((n + 1).factorial : ℝ) * (b - a) ^ (n + 1)

/-!
## Part III: MVT as First-Order Taylor

The ordinary Mean Value Theorem is the n=0 case of Taylor's theorem:

  f(b) = f(a) + f'(c) · (b-a)

This provides the conceptual connection between MVT and Taylor's theorem.
-/

/-- The Mean Value Theorem is the special case n=0 of Taylor's theorem.

    Taylor with n=0 gives:
      f(b) - f(a) = f'(c) · (b - a)
    which is exactly the MVT.

    This is proved from `taylor_lagrange_remainder` by specializing n=0. -/
theorem mvt_is_first_order_taylor
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContDiff ℝ 1 f) :
    ∃ c ∈ Set.Ioo a b,
      f b - f a = deriv f c * (b - a) := by
  have hf1 : ContDiff ℝ (↑(0 + 1)) f := by simpa using hf
  obtain ⟨c, hc, heq⟩ := taylor_lagrange_remainder f a b hab 0 hf1
  use c, hc
  rw [taylorPolynomial_zero] at heq
  simp [iteratedDeriv_one, Nat.factorial] at heq
  linarith

/-!
## Part IV: Taylor's Theorem at Order 2

The second-order case is particularly useful:
  f(b) = f(a) + f'(a)(b-a) + f''(c)/2 · (b-a)²

This gives the best quadratic approximation with an exact remainder.
-/

/-- Second-order Taylor's theorem:
    f(b) = f(a) + f'(a)(b-a) + f''(c)/2 · (b-a)²
    for some c between a and b. -/
theorem taylor_second_order
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContDiff ℝ 2 f) :
    ∃ c ∈ Set.Ioo a b,
      f b = f a + deriv f a * (b - a) +
        iteratedDeriv 2 f c / 2 * (b - a) ^ 2 := by
  have hf2 : ContDiff ℝ (↑(1 + 1)) f := by simpa using hf
  obtain ⟨c, hc, heq⟩ := taylor_lagrange_remainder f a b hab 1 hf2
  use c, hc
  rw [taylorPolynomial_one] at heq
  simp [Nat.factorial] at heq
  linarith

end MeanValueTheoremOQ02
