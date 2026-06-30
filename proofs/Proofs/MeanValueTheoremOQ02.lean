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
- `taylor_lagrange_remainder`: Taylor's theorem with the Lagrange remainder,
  proved (not axiomatized) by bridging Mathlib's `taylorWithinEval` form
- `mvt_is_first_order_taylor`: MVT is Taylor's theorem with n=0

Theorems: 5, Axioms: 0, Sorries: 0
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
  ∑ k ∈ Finset.range (n + 1),
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

/-!
## Part II: Taylor's Theorem with Lagrange Remainder

The classical statement: if f is (n+1)-times differentiable on [a,b],
then there exists c between a and b such that:

  f(b) = T_n(b) + f^(n+1)(c)/(n+1)! · (b-a)^{n+1}

This is the higher-order generalization of the MVT (which is the n=0 case).
-/

/-- **Taylor's Theorem with Lagrange Remainder**.

    If f is (n+1)-times continuously differentiable, then there exists
    c ∈ (a,b) such that:
      f(b) - taylorPolynomial f a n b = iteratedDeriv (n+1) f c / (n+1)! · (b-a)^{n+1}

    Discharged from Mathlib's `taylor_mean_remainder_lagrange_iteratedDeriv`,
    which already states the Lagrange remainder with the *global* iterated
    derivative. The only gap is a formulation bridge: Mathlib's `taylorWithinEval`
    (built from `iteratedDerivWithin` on `Set.Icc a b`) agrees term-by-term with
    this file's `taylorPolynomial` (built from the global `iteratedDeriv`),
    because on the unique-differentiability set `Icc a b` the within-derivative
    equals the global one (`iteratedDerivWithin_eq_iteratedDeriv`). No integral
    remainder or MVT-for-integrals machinery is needed.

    Reference: Rudin "Principles of Mathematical Analysis" Theorem 5.15. -/
theorem taylor_lagrange_remainder
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) :
    ∃ c ∈ Set.Ioo a b,
      f b - taylorPolynomial f a n b =
      iteratedDeriv (n + 1) f c / ((n + 1).factorial : ℝ) * (b - a) ^ (n + 1) := by
  have hu : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hmem : a ∈ Set.Icc a b := ⟨le_refl a, le_of_lt hab⟩
  -- The within-Taylor polynomial on `Icc a b` matches `taylorPolynomial`.
  have hpoly : taylorWithinEval f n (Set.Icc a b) a b = taylorPolynomial f a n b := by
    rw [taylor_within_apply]
    simp only [taylorPolynomial]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hcda : ContDiffAt ℝ k f a :=
      hf.contDiffAt.of_le (by exact_mod_cast Nat.le_succ_of_le hk')
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hcda hmem, smul_eq_mul]
    ring
  obtain ⟨c, hc, heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv hab hf.contDiffOn
  refine ⟨c, hc, ?_⟩
  rw [hpoly] at heq
  rw [heq]; ring

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
