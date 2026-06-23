import Mathlib.Combinatorics.Enumerative.Schroder
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-
# The large Schröder generating function and its defining quadratic

This file builds the generating-function infrastructure for the large Schröder numbers
`L = Nat.largeSchroder` and proves the **algebraic functional equation** it satisfies:

  `f = 1 + f * X + f^2 * X`,   equivalently   `f^2 * X + (1 - f) * f * 0 + ... `

i.e. `X * f^2 + (X - 1) * f + 1 = 0` over a ring with subtraction.  Here

  `f := schroderSeries = ∑_{n ≥ 0} L n * Xⁿ ∈ ℕ⟦X⟧`.

This is **Step 1–2 of the holonomic-recurrence roadmap** recorded in
`SchroderLinearRecurrenceAristotle.lean`.  It is a direct mirror of Mathlib's
`PowerSeries.catalanSeries_sq_mul_X_add_one`
(`Mathlib/RingTheory/PowerSeries/Catalan.lean`); the Catalan series satisfies
`C = 1 + C^2 * X`, while the large Schröder series carries the extra linear `f * X`
term coming from the `+ largeSchroder n` summand in `Nat.largeSchroder_succ`
(`L (n+1) = L n + ∑_{i ≤ n} L i * L (n-i)`).

## What remains (Steps 3–5)

The order-two holonomic recurrence
`(n + 3) * L (n+2) + n * L n = 3 * (2n + 3) * L (n+1)` follows by differentiating this
quadratic (over `ℤ⟦X⟧`), eliminating `f^2` and `f * f'` to get the linear ODE
`X * (X^2 - 6X + 1) * f' = (3X - 1) * f + (X + 1)`, and reading off the `Xⁿ`-coefficient
with `PowerSeries.coeff_derivative`.  Those steps are *not* in this file.
-/

namespace PowerSeries

open Finset Nat

/-- The large Schröder generating function `f = ∑_{n ≥ 0} L n * Xⁿ` as a power series over `ℕ`. -/
def schroderSeries : PowerSeries ℕ := PowerSeries.mk Nat.largeSchroder

@[simp]
lemma schroderSeries_coeff (n : ℕ) : (coeff n) schroderSeries = Nat.largeSchroder n := by
  simp [schroderSeries]

@[simp]
lemma schroderSeries_constantCoeff : constantCoeff schroderSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp

/-- Antidiagonal form of the defining recurrence `Nat.largeSchroder_succ`, matching the
`Finset.antidiagonal` shape produced by `PowerSeries.coeff_mul`.  Mirrors `Nat.catalan_succ'`. -/
theorem _root_.Nat.largeSchroder_succ' (n : ℕ) :
    Nat.largeSchroder (n + 1)
      = Nat.largeSchroder n
        + ∑ ij ∈ antidiagonal n, Nat.largeSchroder ij.1 * Nat.largeSchroder ij.2 := by
  rw [Nat.largeSchroder_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => Nat.largeSchroder x * Nat.largeSchroder y) n]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp [Nat.lt_succ_iff]

/-- **Defining quadratic of the large Schröder generating function.**
`f = 1 + f * X + f^2 * X`, where `f = schroderSeries`.

Equivalently `X * f^2 + (X - 1) * f + 1 = 0` over a ring with subtraction.  This is the
large-Schröder analogue of `PowerSeries.catalanSeries_sq_mul_X_add_one`. -/
theorem schroderSeries_eq :
    schroderSeries = 1 + schroderSeries * X + schroderSeries ^ 2 * X := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [map_add, coeff_one, if_neg n.succ_ne_zero, zero_add, coeff_succ_mul_X, sq,
      coeff_mul, schroderSeries_coeff, Nat.largeSchroder_succ']

end PowerSeries
