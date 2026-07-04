/-
# Gaussian even moments:  `E[X^{2k}] = (2k-1)‼`

The grandparent file `AreaOfCircleOQ05Incomplete01OQ01` formalized the standard
normal `X ~ N(0,1)`, settled the moments `E[X⁰], E[X¹], E[X²]`, and recorded the
moment-generating function

    `M_X(t) = E[e^{tX}] = exp(t²/2)`.

It explicitly left open the **general moment formula**

    `E[X^{2k}]   = (2k-1)‼`   (odd double factorial),
    `E[X^{2k+1}] = 0`.

This file closes that strand.

## Method — MGF derivative recursion

Mathlib's `iteratedDeriv_mgf_zero` identifies the moments with the derivatives of
the MGF at `0`:  writing `g(t) = M_X(t) = exp(t²/2)`,

    `E[Xⁿ] = g⁽ⁿ⁾(0)`.

`g` solves the first-order ODE `g'(t) = t·g(t)`.  Differentiating this identity
`n` times (Leibniz against the linear factor `t`, whose second derivative is `0`)
and evaluating at `0` — where the `t·g⁽ⁿ⁾(t)` term vanishes — gives the
parity-preserving recursion

    `g⁽ⁿ⁺¹⁾(0) = n · g⁽ⁿ⁻¹⁾(0)`,   i.e.   `E[X^{n+1}] = n · E[X^{n-1}]`.

Unwinding:  the even index accumulates `∏_{i<k}(2i+1) = (2k-1)‼`, while the odd
index is annihilated by the base case `E[X] = 0`.

## Main results

* `moment_eq_iteratedDeriv` — `E[Xⁿ] = g⁽ⁿ⁾(0)` for the standard normal.
* `moment_recursion`        — `E[X^{n+1}] = n · E[X^{n-1}]`.
* `stdNormal_even_moment`   — `E[X^{2k}] = ∏_{i<k}(2i+1)`.
* `stdNormal_even_moment_doubleFactorial` — `E[X^{2k}] = (2k-1)‼`.
* `stdNormal_odd_moment`    — `E[X^{2k+1}] = 0`.

Everything is `sorry`-free and axiom-free (only `propext / Classical.choice /
Quot.sound`).
-/

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Proofs.AreaOfCircleOQ05Incomplete01OQ01
import Mathlib.Tactic

open MeasureTheory Real ProbabilityTheory
open scoped ProbabilityTheory Nat

namespace AreaOfCircleOQ05Incomplete01OQ01OQ01

open AreaOfCircleOQ05Incomplete01OQ01 (stdNormal stdNormal_mgf)

/-- The moment-generating function of the standard normal, as the smooth map
    `g(t) = exp(t²/2)`.  (Equals `mgf id stdNormal`; see `g_eq_mgf`.) -/
noncomputable def g : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)

@[simp] lemma g_zero : g 0 = 1 := by simp [g]

/-- `g` is the moment-generating function of the standard normal. -/
lemma g_eq_mgf : g = mgf id stdNormal := stdNormal_mgf.symm

/-- `g` is smooth. -/
lemma g_contDiff : ContDiff ℝ ⊤ g := by
  unfold g
  fun_prop

/-- Each iterated derivative of `g` is differentiable (as `g` is `C^∞`). -/
lemma differentiable_iteratedDeriv_g (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n g) :=
  (g_contDiff.of_le le_top).differentiable_iteratedDeriv' n

/-- The defining first-order ODE:  `g'(t) = t · g(t)`. -/
lemma deriv_g : deriv g = fun t => t * g t := by
  funext t
  have hu : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    have h := (hasDerivAt_pow 2 t).div_const 2
    simpa using h
  have h : HasDerivAt g (Real.exp (t ^ 2 / 2) * t) t := hu.exp
  rw [h.deriv]
  simp only [g]
  ring

/-- Pointwise form of the ODE. -/
lemma deriv_g_apply (t : ℝ) : deriv g t = t * g t := congrFun deriv_g t

/-- helper: `deriv (g⁽ᵏ⁾) = g⁽ᵏ⁺¹⁾`. -/
lemma deriv_iteratedDeriv_g (k : ℕ) :
    deriv (iteratedDeriv k g) = iteratedDeriv (k + 1) g := by
  rw [iteratedDeriv_succ]

/-- **Product-rule recursion for the iterated derivatives of `g`.**
For every `n`,
`g⁽ⁿ⁺²⁾(t) = t · g⁽ⁿ⁺¹⁾(t) + (n+1) · g⁽ⁿ⁾(t)`
(the Leibniz expansion of `(t·g⁽ⁿ⁺¹⁾)'`, with no Nat subtraction). -/
lemma iteratedDeriv_add_two_g (n : ℕ) :
    iteratedDeriv (n + 2) g
      = fun t => t * iteratedDeriv (n + 1) g t + ((n : ℝ) + 1) * iteratedDeriv n g t := by
  -- `HasDerivAt` for each iterated derivative: `(g⁽ᵏ⁾)'(t) = g⁽ᵏ⁺¹⁾(t)`.
  have hD : ∀ (k : ℕ) (t : ℝ),
      HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g t) t := by
    intro k t
    have h := (differentiable_iteratedDeriv_g k t).hasDerivAt
    rwa [deriv_iteratedDeriv_g] at h
  induction n with
  | zero =>
    funext t
    have e2 : iteratedDeriv 2 g = deriv (iteratedDeriv 1 g) := iteratedDeriv_succ
    have e1 : iteratedDeriv 1 g = fun t => t * g t := by
      rw [iteratedDeriv_succ, iteratedDeriv_zero, deriv_g]
    have hg : HasDerivAt g (t * g t) t := by
      have h := (differentiable_iteratedDeriv_g 0 t).hasDerivAt
      rw [iteratedDeriv_zero, deriv_g_apply] at h
      exact h
    have hcomp : HasDerivAt (fun t => t * g t) (1 * g t + t * (t * g t)) t :=
      (hasDerivAt_id t).mul hg
    rw [e2, e1, hcomp.deriv]
    simp only [iteratedDeriv_zero]
    push_cast; ring
  | succ n ih =>
    funext t
    -- `g⁽ⁿ⁺³⁾ = (g⁽ⁿ⁺²⁾)'`; substitute the `ih`-shape and differentiate the sum-product.
    have key : iteratedDeriv (n + 1 + 2) g
        = deriv (fun t => t * iteratedDeriv (n + 1) g t
            + ((n : ℝ) + 1) * iteratedDeriv n g t) := by
      have e : iteratedDeriv (n + 1 + 2) g = deriv (iteratedDeriv (n + 2) g) :=
        iteratedDeriv_succ
      rw [e, ih]
    have hcomp : HasDerivAt
        (fun t => t * iteratedDeriv (n + 1) g t + ((n : ℝ) + 1) * iteratedDeriv n g t)
        (1 * iteratedDeriv (n + 1) g t + t * iteratedDeriv (n + 1 + 1) g t
          + ((n : ℝ) + 1) * iteratedDeriv (n + 1) g t) t :=
      ((hasDerivAt_id t).mul (hD (n + 1) t)).add (((hD n t).const_mul ((n : ℝ) + 1)))
    rw [key, hcomp.deriv]
    push_cast; ring

/-- **Recursion at `0`.**  `g⁽ⁿ⁺²⁾(0) = (n+1) · g⁽ⁿ⁾(0)`.  The `t·g⁽ⁿ⁺¹⁾(t)`
term of `iteratedDeriv_add_two_g` vanishes at `t = 0`. -/
lemma iteratedDeriv_add_two_g_zero (n : ℕ) :
    iteratedDeriv (n + 2) g 0 = (↑n + 1 : ℝ) * iteratedDeriv n g 0 := by
  have h := congrFun (iteratedDeriv_add_two_g n) 0
  simpa using h

/-- Even iterated derivatives at `0` accumulate the product of odd numbers. -/
lemma iteratedDeriv_even_g (k : ℕ) :
    iteratedDeriv (2 * k) g 0 = ∏ i ∈ Finset.range k, (2 * (i : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [e, iteratedDeriv_add_two_g_zero, ih, Finset.prod_range_succ]
    push_cast; ring

/-- Odd iterated derivatives at `0` vanish (annihilated by `g'(0) = 0`). -/
lemma iteratedDeriv_odd_g (k : ℕ) :
    iteratedDeriv (2 * k + 1) g 0 = 0 := by
  induction k with
  | zero =>
    have e : 2 * 0 + 1 = 1 := by norm_num
    rw [e, iteratedDeriv_succ, iteratedDeriv_zero]
    simp [deriv_g_apply]
  | succ n ih =>
    have e : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [e, iteratedDeriv_add_two_g_zero, ih, mul_zero]

/-- **Moments as MGF derivatives.**  `E[Xⁿ] = g⁽ⁿ⁾(0)` for the standard normal. -/
lemma moment_eq_iteratedDeriv (n : ℕ) :
    ∫ x, x ^ n ∂stdNormal = iteratedDeriv n g 0 := by
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet id stdNormal) := by
    have h : integrableExpSet id stdNormal = Set.univ := by
      unfold stdNormal; exact integrableExpSet_id_gaussianReal
    rw [h, interior_univ]; exact Set.mem_univ 0
  rw [g_eq_mgf, iteratedDeriv_mgf_zero hmem n]
  simp

/-! ### Main theorems -/

/-- **Moment recursion.**  `E[X^{n+2}] = (n+1) · E[Xⁿ]`. -/
theorem moment_recursion (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂stdNormal = (↑n + 1 : ℝ) * ∫ x, x ^ n ∂stdNormal := by
  rw [moment_eq_iteratedDeriv, moment_eq_iteratedDeriv, iteratedDeriv_add_two_g_zero]

/-- **Even moment (product form).**  `E[X^{2k}] = ∏_{i<k}(2i+1)`. -/
theorem stdNormal_even_moment (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂stdNormal = ∏ i ∈ Finset.range k, (2 * (i : ℝ) + 1) := by
  rw [moment_eq_iteratedDeriv, iteratedDeriv_even_g]

/-- **Odd moment.**  `E[X^{2k+1}] = 0` for the standard normal. -/
theorem stdNormal_odd_moment (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) ∂stdNormal = 0 := by
  rw [moment_eq_iteratedDeriv, iteratedDeriv_odd_g]

/-- Double-factorial successor identity for odd arguments:
`(2n+1)‼ = (2n+1) · (2n-1)‼`. -/
lemma odd_df_succ (n : ℕ) : (2 * n + 1)‼ = (2 * n + 1) * (2 * n - 1)‼ := by
  cases n with
  | zero => decide
  | succ m =>
    have e1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [e1, e2, Nat.doubleFactorial_add_two]

/-- The product of the first `k` odd numbers is the odd double factorial. -/
lemma prod_odd_eq_doubleFactorial (k : ℕ) :
    (∏ i ∈ Finset.range k, (2 * i + 1)) = (2 * k - 1)‼ := by
  induction k with
  | zero => decide
  | succ n ih =>
    have e : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [Finset.prod_range_succ, ih, e, odd_df_succ n, Nat.mul_comm]

/-- **Even moment (double-factorial form).**  `E[X^{2k}] = (2k-1)‼`.
This closes the general even-moment strand left open by the grandparent. -/
theorem stdNormal_even_moment_doubleFactorial (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂stdNormal = ((2 * k - 1)‼ : ℝ) := by
  rw [stdNormal_even_moment, ← prod_odd_eq_doubleFactorial]
  push_cast
  rfl

end AreaOfCircleOQ05Incomplete01OQ01OQ01
