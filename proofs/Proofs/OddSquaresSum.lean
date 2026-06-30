import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-
# Sum of Squares of the First n Odd Numbers

## Open Question (odd-squares-sum-oq-01)

"The sum of the squares of the first n odd numbers has the closed form
`n(2n−1)(2n+1)/3`."  Writing the k-th odd number as `2k+1` for `k = 0,…,n−1`,

    ∑_{k<n} (2k+1)² = 1² + 3² + 5² + ⋯ + (2n−1)² = n(2n−1)(2n+1)/3.

This is the odd-indexed companion of the square-pyramidal identity
`∑_{k≤n} k² = n(n+1)(2n+1)/6`.

## Result

A fully machine-checked, self-contained proof by induction.

* `three_mul_sum_odd_squares` is the division-free integer form
  `3·∑_{k<n} (2k+1)² + n = 4n³`.  Phrased additively it contains **no truncated
  subtraction**, so the inductive step closes by `ring` alone.
* `sum_odd_squares_rat` is the classical closed form over `ℚ`,
  `∑_{k<n} (2k+1)² = n(2n−1)(2n+1)/3`, proved directly by induction.

## Novelty

Mathlib has the square-pyramidal sum-of-squares identity but *not* this
odd-indexed variant.  This file supplies both an exact ℕ form and the rational
closed form.

0 sorries, 0 axioms.
-/

namespace OddSquaresSum

open Finset

/-- **Division-free integer form.**  Three times the sum of the squares of the
first `n` odd numbers, plus `n`, equals `4n³`:

`3·∑_{k<n} (2k+1)² + n = 4n³`.

Stated additively there is no subtraction, so the inductive step is pure `ring`. -/
theorem three_mul_sum_odd_squares (n : ℕ) :
    3 * (∑ k ∈ range n, (2 * k + 1) ^ 2) + n = 4 * n ^ 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.mul_add]
    -- Reassociate so the inductive hypothesis `3·∑ + m = 4m³` appears verbatim.
    have key :
        3 * (∑ k ∈ range m, (2 * k + 1) ^ 2) + 3 * (2 * m + 1) ^ 2 + (m + 1)
          = (3 * (∑ k ∈ range m, (2 * k + 1) ^ 2) + m) + (3 * (2 * m + 1) ^ 2 + 1) := by
      ring
    rw [key, ih]
    ring

/-- **Closed form over `ℚ`.**  The sum of the squares of the first `n` odd
numbers equals `n(2n−1)(2n+1)/3`:

`∑_{k<n} (2k+1)² = n(2n−1)(2n+1)/3`. -/
theorem sum_odd_squares_rat (n : ℕ) :
    ∑ k ∈ range n, (2 * (k : ℚ) + 1) ^ 2
      = (n : ℚ) * (2 * n - 1) * (2 * n + 1) / 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

end OddSquaresSum
