import Mathlib.Combinatorics.Enumerative.Schroder
import Mathlib.Tactic

/-!
# Positivity and exponential growth of the large Schröder numbers

Mathlib's `Mathlib/Combinatorics/Enumerative/Schroder.lean` defines the large Schröder numbers
`Nat.largeSchroder` via the quadratic (convolution / Segner-type) recurrence

  `L (n+1) = L n + ∑ i ≤ n, L i * L (n - i)`        (`Nat.largeSchroder_succ`)

and records only that they are *even* for `n ≠ 0` (`Nat.even_largeSchroder`).  It does not record
two basic quantitative facts:

* that the numbers are **positive**, and
* the **growth rate**: the ratio `L (n+1) / L n` is at least `3` (in fact it tends to the
  characteristic number `3 + 2√2 ≈ 5.83`, the larger root of `x² - 6x + 1`).

This entry supplies both, working entirely with natural-number arithmetic and only the
convolution recurrence as input.

## Main results

* `Nat.largeSchroder_pos` : `0 < largeSchroder n`.
* `Nat.two_mul_largeSchroder_le_conv` : the convolution sum dominates `2 · L (n+1)` (the two
  boundary terms `i = 0` and `i = n+1` already contribute `2 · L (n+1)`).
* `Nat.largeSchroder_ge_three_mul` : `3 · L (n+1) ≤ L (n+2)` — each step grows by a factor `≥ 3`.
* `Nat.largeSchroder_ge_two_mul_three_pow` : the closed exponential lower bound
  `2 · 3 ^ n ≤ L (n+1)`, hence `L` grows at least geometrically with ratio `3`.

## The deeper open question

The *order-two holonomic* (P-recursive) linear recurrence

  `(n + 3) · L (n+2) + n · L n = 3 · (2n + 3) · L (n+1)`,

which computes `L (n+2)` from the **two** previous values in `O(1)` operations (the
large-Schröder analogue of the Catalan first-order recurrence in `catalan-numbers-oq-01`), is
stated and discussed in the companion file `SchroderLinearRecurrenceAristotle.lean`.  Its proof
requires generating-function / creative-telescoping machinery (the GF `f = ∑ L n xⁿ` satisfies
`x f² + (x-1) f + 1 = 0`, giving the linear ODE `x(x²-6x+1) f' = (3x-1) f + (x+1)`); it is left
for automated proof search.
-/

namespace Nat

open Finset

/-- **Positivity of the large Schröder numbers.**  Mathlib records that `largeSchroder n` is
even for `n ≠ 0` (`Nat.even_largeSchroder`) but not that it is positive. -/
theorem largeSchroder_pos : ∀ n, 0 < largeSchroder n
  | 0 => by simp
  | n + 1 => by
      rw [largeSchroder_succ]
      have : 0 < largeSchroder n := largeSchroder_pos n
      positivity

/-- The convolution sum appearing in the quadratic recurrence is at least `2 * largeSchroder (n+1)`:
the two boundary terms `i = 0` and `i = n+1` already contribute
`L 0 * L (n+1) + L (n+1) * L 0 = 2 * L (n+1)`. -/
theorem two_mul_largeSchroder_le_conv (n : ℕ) :
    2 * largeSchroder (n + 1) ≤ ∑ i ≤ n + 1, largeSchroder i * largeSchroder (n + 1 - i) := by
  have hsub : ({0, n + 1} : Finset ℕ) ⊆ Iic (n + 1) := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    simp only [mem_Iic]; omega
  have hpair : ∑ i ∈ ({0, n + 1} : Finset ℕ), largeSchroder i * largeSchroder (n + 1 - i)
      = 2 * largeSchroder (n + 1) := by
    rw [Finset.sum_pair (by omega)]
    simp [largeSchroder_zero]
    ring
  calc 2 * largeSchroder (n + 1)
      = ∑ i ∈ ({0, n + 1} : Finset ℕ), largeSchroder i * largeSchroder (n + 1 - i) := hpair.symm
    _ ≤ ∑ i ≤ n + 1, largeSchroder i * largeSchroder (n + 1 - i) :=
        Finset.sum_le_sum_of_subset hsub

/-- **Growth lower bound:** `3 * L (n+1) ≤ L (n+2)`.  Each Schröder step grows by a factor of at
least `3`. -/
theorem largeSchroder_ge_three_mul (n : ℕ) :
    3 * largeSchroder (n + 1) ≤ largeSchroder (n + 2) := by
  rw [largeSchroder_succ (n + 1)]
  have h := two_mul_largeSchroder_le_conv n
  omega

/-- **Exponential lower bound:** `2 * 3 ^ n ≤ L (n+1)`.  The large Schröder numbers grow at least
geometrically with ratio `3` (the true ratio tends to `3 + 2√2 ≈ 5.83`). -/
theorem largeSchroder_ge_two_mul_three_pow : ∀ n, 2 * 3 ^ n ≤ largeSchroder (n + 1)
  | 0 => by norm_num [largeSchroder]
  | n + 1 => by
      calc 2 * 3 ^ (n + 1)
          = 3 * (2 * 3 ^ n) := by ring
        _ ≤ 3 * largeSchroder (n + 1) := by
            have := largeSchroder_ge_two_mul_three_pow n; omega
        _ ≤ largeSchroder (n + 2) := largeSchroder_ge_three_mul n

end Nat
