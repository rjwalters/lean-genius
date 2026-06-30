import Mathlib.Combinatorics.Enumerative.Schroder
import Mathlib.Tactic

/-
# Companion file: the order-two holonomic recurrence for large Schröder numbers

This file isolates the HARD (but classical) result for automated proof search.

The headline recurrence `largeSchroder_holonomic` is now proved *unconditionally on top of*
the single convolution lemma `largeSchroder_conv_holonomic` (the reduction is a routine
`linear_combination`, recorded below).  Hence the **only** remaining `sorry` — the sole piece
needing generating-function / creative-telescoping machinery — is `largeSchroder_conv_holonomic`.

The large Schröder numbers `L = Nat.largeSchroder` satisfy the order-two holonomic
(P-recursive) linear recurrence

  `(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)`,

equivalently `(n+1) * L n = 3 * (2n-1) * L (n-1) - (n-2) * L (n-2)` for `n ≥ 2`.
Values: L 0 = 1, L 1 = 2, L 2 = 6, L 3 = 22, L 4 = 90, L 5 = 394.

## Proof sketch (generating functions)

Let `f = ∑ L n xⁿ`.  The convolution recurrence `Nat.largeSchroder_succ` translates to the
algebraic equation `x * f^2 + (x - 1) * f + 1 = 0`.  Differentiating and eliminating `f^2`
and `f * f'` gives the linear ODE `x * (x^2 - 6x + 1) * f' = (3x - 1) * f + (x + 1)`, whose
`xⁿ`-coefficient is exactly the stated recurrence.

## Equivalent convolution form (a useful intermediate)

Writing `Q n = ∑ i ≤ n, L i * L (n - i)` for the convolution (so `L (n+1) = L n + Q n`), the
recurrence is equivalent to

  `(n + 3) * Q (n+1) = (5n + 6) * Q n + (4n + 6) * L n`.

Both statements below are over `ℕ` with no subtraction.

## Buildable-in-Lean roadmap (Mathlib `PowerSeries` API)

This recurrence is *not* a deep gap: every ingredient now exists in Mathlib, so it is BUILDABLE
(~150–250 lines), not blocked.  Concrete plan, mirroring the Catalan precedent.  **Steps 1–2 are
now executed** in the sibling file `Proofs/SchroderGeneratingFunction.lean`; Steps 3–5 remain.

1. **GF object.** [DONE — `PowerSeries.schroderSeries : ℕ⟦X⟧ := PowerSeries.mk largeSchroder`,
   with `schroderSeries_coeff` and `schroderSeries_constantCoeff = 1`.]  (The ODE in Step 3
   onward will re-cast this over `ℤ⟦X⟧`, since differentiation/elimination need subtraction.)

2. **GF quadratic** `f = 1 + f*X + f^2*X`  (equivalently `X * f^2 + (X - 1) * f + 1 = 0`).
   [DONE — `PowerSeries.schroderSeries_eq`, plus the antidiagonal helper
   `Nat.largeSchroder_succ'`.]  This is a *direct mirror* of Mathlib's
   `PowerSeries.catalanSeries_sq_mul_X_add_one : catalanSeries ^ 2 * X + 1 = catalanSeries`
   (file `Mathlib/RingTheory/PowerSeries/Catalan.lean`): `ext n; cases n`, then
   `coeff_succ_mul_X`, `sq`, `coeff_mul`, and `largeSchroder_succ'` in place of `catalan_succ'`.
   The extra linear `f*X` term (vs. Catalan) comes from the `+ largeSchroder n` summand in
   `largeSchroder_succ`.

3. **Differentiate.** `PowerSeries.derivative` (`Mathlib/RingTheory/PowerSeries/Derivative.lean`)
   is a `Derivation` (`d⁄dX`), giving `derivative_X = 1`, `derivative_C = 0`, additivity, and the
   Leibniz rule `derivativeFun_mul`.  Differentiating the quadratic gives
   `(2*X*f + (X-1)) * f' = -(f^2 + f)`.

4. **Eliminate `f²` and the `f·f'` term.** The discriminant identity
   `(2*X*f + (X-1))^2 = X^2 - 6*X + 1`  (which holds *on the solution*, since the RHS is the
   discriminant of the quadratic and the cross term vanishes by step 2) rationalises the
   denominator, yielding the linear ODE  `X*(X^2 - 6*X + 1) * f' = (3*X - 1)*f + (X + 1)`.

5. **Extract the `xⁿ`-coefficient.** `PowerSeries.coeff_derivative`
   (`coeff n (d⁄dX f) = coeff (n+1) f * (n+1)`) turns `f'`-coefficients into `(n+1)*L(n+1)`, and
   `coeff_mul` / `coeff_X_mul` / `coeff_X_pow_mul` expand the polynomial coefficients.  Reading off
   `coeff n` of the ODE in step 4 produces exactly `largeSchroder_holonomic`; the convolution-form
   `largeSchroder_conv_holonomic` below follows the same way from step 2's coefficient identity.

The single remaining `sorry` is therefore HARD-but-classical and fully scoped: it awaits either
automated proof search or a manual session with a working Lean verifier (this session had neither
Aristotle nor a responsive docker build available).

## Update (2026-06-23): direct-ODE route supersedes the convolution detour

Steps 3–5 have now been executed in the sibling file `Proofs/SchroderHolonomicODE.lean`, working
over `ℤ⟦X⟧`.  Crucially, the coefficient extraction of the linear ODE
`X*(X²-6X+1)*g' = (3X-1)*g + (X+1)` yields the **headline recurrence directly**, so the
convolution-form intermediate `largeSchroder_conv_holonomic` below is *not* on the critical path.

The hard algebra (eliminating `g²` and the `g·g'` cross term) is now a single `linear_combination`
whose certificate was verified symbolically:
  `X*(X²-6X+1)*g' − (3X-1)*g − (X+1)
     = X*(2*X*g + (X-1)) · [diff. of quadratic] + (−4*X²*g' − 2*X*g − X − 1) · [quadratic]`.
The discriminant `(2*X*g + (X-1))² = X²-6X+1 = 4*X·[quadratic]` is likewise a certified one-liner.

Only two *mechanical* `sorry`s remain in `SchroderHolonomicODE.lean`:
`schroderIntSeries_diff` (Leibniz/`Derivation` bookkeeping) and `largeSchroder_holonomic_via_ode`
(coefficient extraction via `coeff_derivative`).  Once discharged, `largeSchroder_conv_holonomic`
below can be deleted.
-/

namespace Nat

open Finset

/-- Convolution-form reformulation of the holonomic recurrence (see module docstring). -/
theorem largeSchroder_conv_holonomic (n : ℕ) :
    (n + 3) * (∑ i ≤ n + 1, largeSchroder i * largeSchroder (n + 1 - i))
      = (5 * n + 6) * (∑ i ≤ n, largeSchroder i * largeSchroder (n - i))
        + (4 * n + 6) * largeSchroder n := by
  sorry

/-- **Order-two holonomic recurrence for the large Schröder numbers.**
`(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)`.

This is a *mechanical consequence* of the convolution-form recurrence
`largeSchroder_conv_holonomic` together with the defining quadratic recurrence
`Nat.largeSchroder_succ` (which gives `L (n+1) = L n + Q n` and
`L (n+2) = L (n+1) + Q (n+1)`).  Substituting both and eliminating the
convolution sum `Q (n+1)` via the convolution form leaves a linear identity
in `L n`, `Q n`, `Q (n+1)` that `linear_combination` discharges.  Thus the
only genuinely hard content is `largeSchroder_conv_holonomic`. -/
theorem largeSchroder_holonomic (n : ℕ) :
    (n + 3) * largeSchroder (n + 2) + n * largeSchroder n
      = 3 * (2 * n + 3) * largeSchroder (n + 1) := by
  have hconv := largeSchroder_conv_holonomic n
  rw [largeSchroder_succ (n + 1), largeSchroder_succ n]
  -- After the two rewrites, both the goal and `hconv` are expressed in `largeSchroder n`
  -- and the two convolution sums `Q n` and `Q (n+1)`; abstract the latter so the remaining
  -- step is a pure linear identity.
  set S := ∑ i ≤ n, largeSchroder i * largeSchroder (n - i)
  set T := ∑ i ≤ n + 1, largeSchroder i * largeSchroder (n + 1 - i)
  zify at hconv ⊢
  linear_combination hconv

end Nat
