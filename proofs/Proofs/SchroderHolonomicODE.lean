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

## Status (research sessions 2026-06-23)

These sessions had **no working Lean verifier** (docker build unresponsive, no prebuilt Mathlib
oleans) and **no Aristotle** (service 404).  The file is therefore *not* kernel-verified yet; it
awaits the deployer build-gate.  Progress this session: the final coefficient-extraction `sorry`
(`Nat.largeSchroder_holonomic_via_ode`) is now **discharged**, so the file is **sorry-free**
(pending build-gate verification).  The extraction is factored through a reusable, fully general
power-series lemma `PowerSeries.coeff_recurrence_of_ode` (independent of the specific Schröder
coefficients), with the `Nat`-level statement obtained by `exact_mod_cast`.

What *is* established with certainty this session:

* The target recurrences are **numerically verified** for `n = 0..3`
  (`L = 1,2,6,22,90,394,1806`; convolution `Q = 1,4,16,68,304`).
* The **discriminant** and **ODE** `linear_combination` certificates below were verified
  *symbolically* (sympy): the ring identity `goalLHS − goalRHS − (certificate) = 0` reduces to `0`.
  These are the genuinely hard algebraic steps (elimination of `g²` and `g·g'`).
* The coefficient-extraction recurrence was **hand-verified term by term** (see the proof outline
  on `coeff_recurrence_of_ode`): each `coeff (n+2) (Xᵏ · g⁽ⁱ⁾)` is computed via `coeff_X_pow_mul'`
  + `coeff_derivative`, and the residual is the ring identity
  `n·aₙ + (n+3)·a_{n+2} = 3·(2n+3)·a_{n+1}` (closed by `linear_combination`, coefficient `1`).
  The only `n`-dependent boundary is the `X³·g'` term, which vanishes at `n = 0` exactly where
  `n·aₙ` does (`rcases n`).
* The differentiation step `schroderIntSeries_diff` (pure `Derivation` / Leibniz bookkeeping)
  is **proved** by applying `derivative ℤ` to the defining quadratic and expanding with the
  `Derivation` simp set.

## Architectural note

This **direct ODE route proves the headline recurrence directly**, without the convolution-form
intermediate `Nat.largeSchroder_conv_holonomic` (the sole remaining `sorry` in
`SchroderLinearRecurrenceAristotle.lean`).  With the extraction `sorry` now discharged here, that
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

Summing and using `smul_eq_mul` / `nsmul_eq_mul` gives the stated identity.

Note this differentiated identity holds for **any** `g` satisfying the defining quadratic — it is
just `D` (a `Derivation`) applied to `schroderIntSeries_quadratic`, with no use of the specific
coefficients of `g`.  The proof applies `congrArg (⇑(derivative ℤ))` and expands the single
hypothesis with the `Derivation` simp set; `linear_combination` then closes the ring identity. -/
theorem schroderIntSeries_diff :
    schroderIntSeries ^ 2
        + 2 * X * schroderIntSeries * (derivative ℤ) schroderIntSeries
      + (X - 1) * (derivative ℤ) schroderIntSeries + schroderIntSeries = 0 := by
  have h := congrArg (⇑(derivative ℤ)) schroderIntSeries_quadratic
  simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, Derivation.map_one_eq_zero, pow_one, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, mul_one] at h
  linear_combination h

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

/-- **Coefficient extraction from the linear ODE (general form).**

For *any* series `g ∈ ℤ⟦X⟧` satisfying the large-Schröder linear ODE
`X·(X²-6X+1)·g' = (3X-1)·g + (X+1)`, the coefficients `aₙ := coeff n g` obey the
order-two holonomic recurrence

  `(n + 3)·a_{n+2} + n·aₙ = 3·(2n+3)·a_{n+1}`.

**Proof outline.** Apply `coeff (n+2)` to the ODE.  After expanding the polynomial factor
`X·(X²-6X+1) = X³ - 6·X² + X` and pushing `coeff` through the linear structure
(`map_add`/`map_sub`/`coeff_C_mul`), each term is a coefficient of `Xᵏ · g` or `Xᵏ · g'`,
evaluated with `coeff_X_pow_mul'` and `coeff_derivative`:

* `coeff (n+2) (X³·g') = n·aₙ`        (boundary-gated at `n = 0`, where it is `0 = 0·a₀`);
* `coeff (n+2) (X²·g') = (n+1)·a_{n+1}`;
* `coeff (n+2) (X·g')  = (n+2)·a_{n+2}`;
* `coeff (n+2) (X·g)   = a_{n+1}`,  and the bare `X`, `1` contribute `0` (since `n+2 ≥ 2`).

Equating LHS and RHS gives
`n·aₙ - 6·(n+1)·a_{n+1} + (n+2)·a_{n+2} = 3·a_{n+1} - a_{n+2}`, i.e. the claimed recurrence
(the residual ring rearrangement is closed by `linear_combination`). -/
theorem coeff_recurrence_of_ode (g : ℤ⟦X⟧)
    (hode : X * (X ^ 2 - 6 * X + 1) * (derivative ℤ) g
        = (3 * X - 1) * g + (X + 1)) (n : ℕ) :
    ((n : ℤ) + 3) * (coeff (n + 2)) g + (n : ℤ) * (coeff n) g
      = 3 * (2 * (n : ℤ) + 3) * (coeff (n + 1)) g := by
  -- The `X³·g'` term is the only one with a vanishing boundary at `n = 0`.
  have hX3 : (coeff (n + 2)) (X ^ 3 * (derivative ℤ) g) = (n : ℤ) * (coeff n) g := by
    rcases n with _ | m
    · rw [coeff_X_pow_mul']; simp
    · rw [coeff_X_pow_mul', if_pos (show 3 ≤ m + 1 + 2 by omega),
        show m + 1 + 2 - 3 = m by omega, coeff_derivative]
      push_cast; ring
  have hX2 : (coeff (n + 2)) (X ^ 2 * (derivative ℤ) g)
      = ((n : ℤ) + 1) * (coeff (n + 1)) g := by
    rw [coeff_X_pow_mul', if_pos (show 2 ≤ n + 2 by omega),
      show n + 2 - 2 = n by omega, coeff_derivative]
    push_cast; ring
  have hX1 : (coeff (n + 2)) (X ^ 1 * (derivative ℤ) g)
      = ((n : ℤ) + 2) * (coeff (n + 2)) g := by
    rw [coeff_X_pow_mul', if_pos (show 1 ≤ n + 2 by omega),
      show n + 2 - 1 = n + 1 by omega, coeff_derivative]
    push_cast; ring
  have hXg : (coeff (n + 2)) (X ^ 1 * g) = (coeff (n + 1)) g := by
    rw [coeff_X_pow_mul', if_pos (show 1 ≤ n + 2 by omega), show n + 2 - 1 = n + 1 by omega]
  have hX0 : (coeff (n + 2)) (X : ℤ⟦X⟧) = 0 := by
    rw [coeff_X, if_neg (show ¬ (n + 2 = 1) by omega)]
  have h1 : (coeff (n + 2)) (1 : ℤ⟦X⟧) = 0 := by
    rw [coeff_one, if_neg (show ¬ (n + 2 = 0) by omega)]
  -- Expand the polynomial factor and split off the constants `6 = C 6`, `3 = C 3`.
  have key := congrArg (coeff (n + 2)) hode
  rw [show X * (X ^ 2 - 6 * X + 1) * (derivative ℤ) g
        = X ^ 3 * (derivative ℤ) g - C (6 : ℤ) * (X ^ 2 * (derivative ℤ) g)
          + X ^ 1 * (derivative ℤ) g by
        rw [show (6 : ℤ⟦X⟧) = C (6 : ℤ) by simp]; ring,
      show (3 * X - 1) * g + (X + 1)
        = C (3 : ℤ) * (X ^ 1 * g) - g + X + 1 by
        rw [show (3 : ℤ⟦X⟧) = C (3 : ℤ) by simp]; ring] at key
  simp only [map_add, map_sub, coeff_C_mul] at key
  rw [hX3, hX2, hX1, hXg, hX0, h1] at key
  linear_combination key

end PowerSeries

namespace Nat

open PowerSeries Finset

/-- **Order-two holonomic recurrence for the large Schröder numbers, via the generating-function
ODE.**  `(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)`.

Read off the `X^{n+2}`-coefficient of `schroderIntSeries_ode`.  **Full extraction (worked out
2026-06-23):** apply `coeff (n+2)` to the ODE.  Because `coeff` is *linear but not
multiplicative*, first distribute `X*(X²-6X+1)*g' = X³*g' − 6*(X²*g') + X*g'` and use the
boundary-aware lemma

  `coeff_X_pow_mul' (p) (k d) : coeff d (X^k * p) = if k ≤ d then coeff (d-k) p else 0`

together with `coeff_derivative : coeff m g' = coeff (m+1) g * (m+1)` and `hL : coeff k g = L k`:

  LHS `coeff (n+2)`:  `(if 1 ≤ n then n*L n else 0) − 6*(n+1)*L(n+1) + (n+2)*L(n+2)`
       (the three terms are `coeff (n-1) g'`, `coeff n g'`, `coeff (n+1) g'`; only the X³ term
        is boundary-gated, vanishing at `n = 0` — and there `n*L n = 0` too, so the gate is
        equivalent to `n*L n` *uniformly* in `n`).
  RHS `coeff (n+2)`:  `3*L(n+1) − L(n+2)`   (the `X` and `1` of `(X+1)` contribute `0` since `n+2 ≥ 2`).

Equating and simplifying (valid for **all** `n ≥ 0`):
`n*L n − 6*(n+1)*L(n+1) + (n+2)*L(n+2) = 3*L(n+1) − L(n+2)`, i.e.
`(n+3)*L(n+2) + n*L n = (6n+9)*L(n+1) = 3*(2n+3)*L(n+1)` — the statement.
Numerically verified for `n = 0..3` (`L = 1,2,6,22,90`).

The extraction itself is performed once, in full generality, by
`PowerSeries.coeff_recurrence_of_ode` (any `g` satisfying the ODE).  Here we instantiate it at
`g = schroderIntSeries`, rewrite the coefficients via `schroderIntSeries_coeff`, and descend from
the `ℤ`-coefficient identity to the `ℕ`-statement with `exact_mod_cast`.  This direct ODE route
supersedes the convolution-form intermediate `Nat.largeSchroder_conv_holonomic`. -/
theorem largeSchroder_holonomic_via_ode (n : ℕ) :
    (n + 3) * largeSchroder (n + 2) + n * largeSchroder n
      = 3 * (2 * n + 3) * largeSchroder (n + 1) := by
  have h := PowerSeries.coeff_recurrence_of_ode PowerSeries.schroderIntSeries
    PowerSeries.schroderIntSeries_ode n
  simp only [PowerSeries.schroderIntSeries_coeff] at h
  exact_mod_cast h

end Nat
