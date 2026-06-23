import Proofs.SchroderGeneratingFunction
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-
# The linear ODE of the large Schröder generating function, and the holonomic recurrence

This file executes **Steps 3–5 of the holonomic-recurrence roadmap** (see
`Proofs/SchroderLinearRecurrenceAristotle.lean`), building on the defining quadratic
`PowerSeries.schroderSeries_eq` proved in `Proofs/SchroderGeneratingFunction.lean`.

Working over `ℤ⟦X⟧` (subtraction is needed for differentiation), let
`g := schroderIntSeries = ∑ L n Xⁿ` with `L = Nat.largeSchroder`.  We:

* recast the defining quadratic over `ℤ`:        `X * g² + (X - 1) * g + 1 = 0`   (`schroderIntSeries_quadratic`);
* record the **discriminant identity**           `(2*X*g + (X - 1))² = X² - 6*X + 1`  (`schroderIntSeries_discriminant`);
* differentiate the quadratic:                   `g² + 2*X*g*g' + (X - 1)*g' + g = 0` (`schroderIntSeries_diff`);
* eliminate `g²` and the cross term to get the **linear ODE**
    `X * (X² - 6*X + 1) * g' = (3*X - 1) * g + (X + 1)`   (`schroderIntSeries_ode`);
* read off the `Xⁿ`-coefficient to obtain the order-two holonomic recurrence
    `(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)`  (`Nat.largeSchroder_holonomic_via_ode`).

## Status (research session 2026-06-23)

This session had **no working Lean verifier** (docker build unresponsive) and **no Aristotle**
(service 404).  The file is therefore *not* kernel-verified yet; it awaits the deployer build-gate.

What *is* established with certainty this session:

* The target recurrences are **numerically verified** for `n = 0..3`
  (`L = 1,2,6,22,90,394,1806`; convolution `Q = 1,4,16,68,304`).
* The **discriminant** and **ODE** `linear_combination` certificates below were verified
  *symbolically* (sympy): the ring identity `goalLHS − goalRHS − (certificate) = 0` reduces to `0`.
  These are the genuinely hard algebraic steps (elimination of `g²` and `g·g'`), and they are
  now **certified** modulo the two mechanical lemmas marked `sorry`:
    1. `schroderIntSeries_diff` — formal differentiation of the quadratic (pure `Derivation` /
       Leibniz bookkeeping; documented inline);
    2. `Nat.largeSchroder_holonomic_via_ode` — coefficient extraction via `coeff_derivative`
       and `coeff_mul`/`coeff_X_pow_mul` (documented inline).
  Both are HARD-but-mechanical and ideal for Aristotle.

## Architectural note

This **direct ODE route proves the headline recurrence directly**, without the convolution-form
intermediate `Nat.largeSchroder_conv_holonomic` (the sole remaining `sorry` in
`SchroderLinearRecurrenceAristotle.lean`).  Once the two `sorry`s below are discharged, the
convolution detour can be retired.  Mathlib's `PowerSeries.catalanSeries_sq_mul_X_add_one`
stops at the analogous quadratic (its only TODO is the closed form), so there is **no Mathlib
precedent** for the ODE/extraction steps performed here.
-/

namespace PowerSeries

open Finset Nat

/-- The large Schröder generating function with **integer** coefficients,
`g = ∑ L n Xⁿ ∈ ℤ⟦X⟧`, obtained from the `ℕ`-valued `schroderSeries` by `map`. -/
noncomputable def schroderIntSeries : ℤ⟦X⟧ :=
  PowerSeries.map (Nat.castRingHom ℤ) schroderSeries

@[simp]
lemma schroderIntSeries_coeff (n : ℕ) :
    (coeff n) schroderIntSeries = (Nat.largeSchroder n : ℤ) := by
  simp [schroderIntSeries, coeff_map]

/-- **Defining quadratic over `ℤ⟦X⟧`.**  `X * g² + (X - 1) * g + 1 = 0`.

Obtained by applying the ring homomorphism `map (Nat.castRingHom ℤ)` to the `ℕ`-level identity
`schroderSeries = 1 + schroderSeries * X + schroderSeries² * X` (`schroderSeries_eq`) and
rearranging.  The `linear_combination -h` certificate is exact:
`(X*g² + (X-1)*g + 1) − 0 + (g − (1 + g*X + g²*X)) = 0` by `ring`. -/
theorem schroderIntSeries_quadratic :
    X * schroderIntSeries ^ 2 + (X - 1) * schroderIntSeries + 1 = 0 := by
  have h : schroderIntSeries
      = 1 + schroderIntSeries * X + schroderIntSeries ^ 2 * X := by
    have hmap := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) schroderSeries_eq
    simpa only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X, schroderIntSeries]
      using hmap
  linear_combination -h

/-- **Discriminant identity.**  On the solution of the defining quadratic,
`(2*X*g + (X - 1))² = X² - 6*X + 1`.

Certificate (sympy-verified):
`(2*X*g + (X-1))² − (X² - 6*X + 1) = 4*X * (X*g² + (X-1)*g + 1)`, and the right factor is `0`. -/
theorem schroderIntSeries_discriminant :
    (2 * X * schroderIntSeries + (X - 1)) ^ 2 = X ^ 2 - 6 * X + 1 := by
  linear_combination (4 * X) * schroderIntSeries_quadratic

/-- **Differentiated quadratic.**  `g² + 2*X*g*g' + (X - 1)*g' + g = 0`, where `g' = d⁄dX g`.

This is the formal derivative of `schroderIntSeries_quadratic`, computed with the `Derivation`
API.  Writing `D = derivative ℤ` and using `D 1 = 0`, `D X = 1`, additivity, and Leibniz
`D (a*b) = a • D b + b • D a` (with `•` = ring multiplication here):

  `D(X*g²) = X * D(g²) + g² * D X = X * (2*g*g') + g²`           (`leibniz`, `leibniz_pow`, `derivative_X`)
  `D((X-1)*g) = (X-1) * D g + g * D (X-1) = (X-1)*g' + g`        (`leibniz`, `derivative_X`, `map_one_eq_zero`)
  `D 1 = 0`                                                       (`Derivation.map_one_eq_zero`)

Summing and using `smul_eq_mul` / `nsmul_eq_mul` gives the stated identity.  Purely mechanical
`Derivation` bookkeeping — left as a scoped `sorry` for a verifier-backed session or Aristotle.
The proof skeleton is:
  `have h := congrArg (⇑(derivative ℤ)) schroderIntSeries_quadratic`
  then `simp` with `[map_add, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
       derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]`
  and finish with `linear_combination h` / `ring_nf`. -/
theorem schroderIntSeries_diff :
    schroderIntSeries ^ 2
        + 2 * X * schroderIntSeries * (derivative ℤ) schroderIntSeries
      + (X - 1) * (derivative ℤ) schroderIntSeries + schroderIntSeries = 0 := by
  sorry

/-- **Linear ODE of the large Schröder generating function.**
`X * (X² - 6*X + 1) * g' = (3*X - 1) * g + (X + 1)`.

This is the crux: it eliminates `g²` and the `g·g'` cross term from the differentiated quadratic.
Certificate (sympy-verified): with
  `D  := schroderIntSeries_diff`  (LHS `= 0`:  `g² + 2*X*g*g' + (X-1)*g' + g`) and
  `Q  := schroderIntSeries_quadratic` (LHS `= 0`: `X*g² + (X-1)*g + 1`),
the ring identity
  `X*(X²-6X+1)*g' − (3X-1)*g − (X+1)
     = X*(2*X*g + (X-1)) · D  +  (−4*X²*g' − 2*X*g − X − 1) · Q`
holds (both sides reduce to `0` after `ring`).  Hence the `linear_combination` below. -/
theorem schroderIntSeries_ode :
    X * (X ^ 2 - 6 * X + 1) * (derivative ℤ) schroderIntSeries
      = (3 * X - 1) * schroderIntSeries + (X + 1) := by
  linear_combination
    (X * (2 * X * schroderIntSeries + (X - 1))) * schroderIntSeries_diff
      + (-4 * X ^ 2 * (derivative ℤ) schroderIntSeries
          - 2 * X * schroderIntSeries - X - 1) * schroderIntSeries_quadratic

end PowerSeries

namespace Nat

open PowerSeries Finset

/-- **Order-two holonomic recurrence for the large Schröder numbers, via the generating-function
ODE.**  `(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)`.

Read off the `Xⁿ`-coefficient of `schroderIntSeries_ode`.  Using
`coeff_derivative : coeff n (d⁄dX g) = coeff (n+1) g * (n+1)` together with
`coeff_X_pow_mul` / `coeff_X_mul` / `coeff_mul`, the coefficient of `Xⁿ` (for `n ≥ 2`) reads

  LHS:  `(n-2)*L(n-2) − 6*(n-1)*L(n-1) + n*L(n)`        (from `(X³ - 6X² + X) * g'`)
  RHS:  `3*L(n-1) − L(n)`                               (from `(3X - 1)*g + (X + 1)`)

so `(n-2)*L(n-2) − 6*(n-1)*L(n-1) + n*L(n) = 3*L(n-1) − L(n)`, i.e.
`(n+1)*L(n) + (n-2)*L(n-2) = 3*(2n-1)*L(n-1)`; reindexing `n ↦ n+2` gives the statement.
Numerically verified for `n = 0..3`.

Coefficient extraction over `ℤ` is mechanical (case split on `n`, `coeff_derivative`,
`coeff_mul`, push casts, `omega`/`linarith`); left as a scoped `sorry` for a verifier-backed
session or Aristotle.  This route supersedes the convolution-form intermediate
`Nat.largeSchroder_conv_holonomic`. -/
theorem largeSchroder_holonomic_via_ode (n : ℕ) :
    (n + 3) * largeSchroder (n + 2) + n * largeSchroder n
      = 3 * (2 * n + 3) * largeSchroder (n + 1) := by
  sorry

end Nat
