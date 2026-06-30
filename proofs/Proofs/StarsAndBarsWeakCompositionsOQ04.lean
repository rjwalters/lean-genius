import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositions
import Proofs.StarsAndBarsWeakCompositionsOQ01

/-
# The Convolution Law for Weak-Composition Generating Functions

## (stars-and-bars-weak-compositions-oq-04)

The sibling entry `StarsAndBarsWeakCompositionsOQ01` identified the ordinary generating
function of the weak-composition counts,

  `W k = ∑ₙ #{f : Fin k → ℕ // ∑ᵢ f i = n} · Xⁿ ∈ S⟦X⟧`,

with Mathlib's algebraic series `invOneSubPow S k = 1/(1 − X)ᵏ`. That entry stopped at the
single-exponent statement `W k = (1 − X)⁻ᵏ`. This file records the **multiplicative**
structure of the family `k ↦ W k` and reads off its enumerative shadow.

## What this adds

* **Convolution / exponent-additivity** (`weakCompositionGenFun_mul`):
  `W k₁ · W k₂ = W (k₁ + k₂)`  for `k₁, k₂ > 0`.
  Combinatorially this is *concatenation*: gluing a weak composition into `k₁` parts onto one
  into `k₂` parts produces a weak composition into `k₁ + k₂` parts, and the bookkeeping of the
  total `n` is exactly the Cauchy product of the two generating functions. Algebraically it is
  the exponent-additivity of `(1 − X)⁻ᵏ`, i.e. Mathlib's `invOneSubPow_add`.

* **Power law** (`weakCompositionGenFun_eq_pow`): `W k = (W 1)ᵏ` for `k > 0`. A single part has
  generating function `W 1 = 1/(1 − X) = 1 + X + X² + ⋯`, and `k` independent parts multiply,
  so `W k = (W 1)ᵏ`.

* **Negative-binomial Vandermonde convolution** (`weakComposition_convolution`): reading off the
  coefficient of `Xᵗ` in the product law gives the purely combinatorial identity

  `∑_{(i,j) ∈ antidiagonal t} C(i + k₁ − 1, i) · C(j + k₂ − 1, j) = C(t + (k₁ + k₂) − 1, t)`.

  This is the "stars and bars" / negative-binomial form of the Chu–Vandermonde convolution
  (distinct from the standard `C(m + n, r) = ∑ C(m, i)·C(n, r − i)`); it is *not* recorded in
  Mathlib. The generating-function bridge of OQ01 turns the analytic product law into this
  finite binomial identity for free.

## Status

0 `sorry`, 0 `axiom`. Everything is a machine-checked consequence of the OQ01 bridge and the
Mathlib `invOneSubPow` / `coeff_mul` API.
-/

open Finset PowerSeries
open scoped BigOperators

namespace StarsAndBarsGenFun

variable (S : Type*) [CommRing S]

/-- The coefficient of `Xⁿ` in `W k` spelled out as the negative-binomial number
`C(n + k − 1, n)` (combining `coeff_weakCompositionGenFun` with the parent's
`card_weakComposition`). Holds for every `k` (no positivity needed). -/
theorem coeff_weakCompositionGenFun_eq_choose (k n : ℕ) :
    coeff n (weakCompositionGenFun S k) = ((n + k - 1).choose n : S) := by
  rw [coeff_weakCompositionGenFun, StarsAndBars.card_weakComposition]

/-- **Convolution law / exponent-additivity.** For positive `k₁, k₂`, the generating function
of weak compositions is multiplicative in the number of parts:
`W k₁ · W k₂ = W (k₁ + k₂)`. This is the Cauchy-product incarnation of concatenating a weak
composition into `k₁` parts with one into `k₂` parts, and on the algebraic side it is the
exponent-additivity of `1/(1 − X)ᵏ` (`invOneSubPow_add`). -/
theorem weakCompositionGenFun_mul (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h2 : 0 < k₂) :
    weakCompositionGenFun S k₁ * weakCompositionGenFun S k₂
      = weakCompositionGenFun S (k₁ + k₂) := by
  rw [weakCompositionGenFun_eq_invOneSubPow S k₁ h1,
    weakCompositionGenFun_eq_invOneSubPow S k₂ h2,
    weakCompositionGenFun_eq_invOneSubPow S (k₁ + k₂) (by omega),
    invOneSubPow_add, Units.val_mul]

/-- **Power law.** For positive `k`, `W k = (W 1)ᵏ`: a weak composition into `k` parts is `k`
independent single parts, each with generating function `W 1 = 1/(1 − X)`, so the generating
functions multiply. -/
theorem weakCompositionGenFun_eq_pow (k : ℕ) (hk : 0 < k) :
    weakCompositionGenFun S k = (weakCompositionGenFun S 1) ^ k := by
  have hu : invOneSubPow S k = (invOneSubPow S 1) ^ k := by
    rw [invOneSubPow_eq_inv_one_sub_pow, invOneSubPow_eq_inv_one_sub_pow, pow_one]
  rw [weakCompositionGenFun_eq_invOneSubPow S k hk,
    weakCompositionGenFun_eq_invOneSubPow S 1 one_pos, hu, Units.val_pow_eq_pow_val]

/-- **Negative-binomial Vandermonde convolution.** Reading off the coefficient of `Xᵗ` in the
product law `W k₁ · W k₂ = W (k₁ + k₂)` yields the finite binomial identity

`∑_{(i,j) ∈ antidiagonal t} C(i + k₁ − 1, i) · C(j + k₂ − 1, j) = C(t + (k₁ + k₂) − 1, t)`.

This is the stars-and-bars / negative-binomial form of the Chu–Vandermonde convolution; it is
not in Mathlib. The proof passes through the generating-function bridge of OQ01 over `ℤ` and
casts the resulting power-series coefficient identity back to `ℕ`. -/
theorem weakComposition_convolution (k₁ k₂ : ℕ) (h1 : 0 < k₁) (h2 : 0 < k₂) (t : ℕ) :
    ∑ ij ∈ antidiagonal t,
        (ij.1 + k₁ - 1).choose ij.1 * (ij.2 + k₂ - 1).choose ij.2
      = (t + (k₁ + k₂) - 1).choose t := by
  -- Coefficient of `Xᵗ` on both sides of the product law, computed over `ℤ`.
  have key : (coeff t) (weakCompositionGenFun ℤ k₁ * weakCompositionGenFun ℤ k₂)
      = (coeff t) (weakCompositionGenFun ℤ (k₁ + k₂)) := by
    rw [weakCompositionGenFun_mul ℤ k₁ k₂ h1 h2]
  rw [coeff_mul] at key
  simp only [coeff_weakCompositionGenFun_eq_choose] at key
  exact_mod_cast key

end StarsAndBarsGenFun
