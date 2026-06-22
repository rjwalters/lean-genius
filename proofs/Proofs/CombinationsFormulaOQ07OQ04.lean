import Mathlib
import Proofs.CombinationsFormulaOQ07

/-
# The Second Moment of the Sum of Squares of Binomial Coefficients

## Open Question OQ-07-OQ-04

The central identity of OQ-07 sums the *squares* of a Pascal row:

  C(2n, n) = ∑_{k=0}^{n} C(n, k)² .

Its sibling OQ-07-OQ-03 weights that sum by `k` (the *first moment*):

  2 · ∑_{k=0}^{n} k · C(n, k)² = n · C(2n, n).

This file weights it by `k²` (the *second moment*).  The result is again a
single central binomial coefficient — now of the predecessor row:

  ∑_{k=0}^{n} k² · C(n, k)² = n² · C(2n − 2, n − 1)        (n ≥ 1).      (★)

Mathlib provides the unweighted row sum (`Nat.sum_range_choose`), Vandermonde's
convolution (`Nat.add_choose_eq`) and the absorption identity
`(k+1)·C(n+1,k+1) = (n+1)·C(n,k)` (`Nat.add_one_mul_choose_eq`), but **not**
this second-moment identity.

## The absorption proof

Unlike the first moment, no reflection is needed: a single application of
absorption collapses each term.  From `k · C(n, k) = n · C(n−1, k−1)` we get

  k² · C(n, k)² = (k · C(n, k))² = (n · C(n−1, k−1))² = n² · C(n−1, k−1)² .

The `k = 0` term vanishes, so reindexing `k = j + 1` and pulling out the
constant `n²` leaves exactly the parent sum of squares over the row `n − 1`:

  ∑_{k=0}^{n} k² · C(n, k)² = n² · ∑_{j=0}^{n−1} C(n−1, j)² = n² · C(2n−2, n−1),

the last step being `central_binom_eq_sum_sq` (OQ-07) applied to `n − 1`.

## Mathematical Context

Read `C(n, k)² / C(2n, n)` as a probability distribution on `{0, …, n}` — the
hypergeometric distribution from splitting a `2n`-set into two halves of size
`n`.  OQ-07-OQ-03 gives its **mean** `n / 2`; identity (★) gives its **second
moment**

  E[k²] = n² · C(2n−2, n−1) / C(2n, n) = n³ / (2(2n−1)),

using `C(2n−2,n−1) / C(2n,n) = n² / (2n(2n−1))`.  Combining the two yields the
clean closed form for the **variance**

  Var[k] = E[k²] − (n/2)² = n² / (4(2n−1)),

the textbook variance of this hypergeometric law.  The absorption identity that
proves (★) is the algebraic engine behind that formula.

## Results

1. `sum_sq_weighted_sq_succ` — the subtraction-free form
   `∑_{k=0}^{m+1} k² · C(m+1, k)² = (m+1)² · C(2m, m)`, valid for every `m`.
2. `sum_sq_weighted_sq` — the classical form (★), `n ≥ 1`.
3. `sum_sq_weighted_centralBinom` — (1) packaged with `Nat.centralBinom`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04

open Finset

/-- **Second moment (subtraction-free form).** For every `m`,
    `∑_{k=0}^{m+1} k² · C(m+1, k)² = (m+1)² · C(2m, m)`.

    The factor `(m+1)²` is what survives the absorption
    `(j+1)·C(m+1,j+1) = (m+1)·C(m,j)`; writing `n = m+1` keeps the statement
    free of natural-number subtraction. -/
theorem sum_sq_weighted_sq_succ (m : ℕ) :
    ∑ k ∈ range (m + 2), k ^ 2 * ((m + 1).choose k) ^ 2
      = (m + 1) ^ 2 * (2 * m).choose m := by
  -- Absorption applied term-by-term to the reindexed (`k = j + 1`) summand.
  have term : ∀ j ∈ range (m + 1),
      (j + 1) ^ 2 * ((m + 1).choose (j + 1)) ^ 2 = (m + 1) ^ 2 * (m.choose j) ^ 2 := by
    intro j _
    have hkey : (j + 1) * (m + 1).choose (j + 1) = (m + 1) * m.choose j := by
      rw [Nat.add_one_mul_choose_eq]; ring
    calc (j + 1) ^ 2 * ((m + 1).choose (j + 1)) ^ 2
        = ((j + 1) * (m + 1).choose (j + 1)) ^ 2 := by rw [mul_pow]
      _ = ((m + 1) * m.choose j) ^ 2 := by rw [hkey]
      _ = (m + 1) ^ 2 * (m.choose j) ^ 2 := by rw [mul_pow]
  rw [Finset.sum_range_succ', Finset.sum_congr rfl term, ← Finset.mul_sum,
      ← CombinationsFormulaOQ07.central_binom_eq_sum_sq]
  simp

/-- **Second moment of the central sum of squares (classical form).**
    For `n ≥ 1`, `∑_{k=0}^{n} k² · C(n, k)² = n² · C(2n − 2, n − 1)`. -/
theorem sum_sq_weighted_sq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), k ^ 2 * (n.choose k) ^ 2 = n ^ 2 * (2 * n - 2).choose (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (m + 1) - 2 = 2 * m from by omega, show m + 1 - 1 = m from by omega,
      show m + 1 + 1 = m + 2 from by omega]
  exact sum_sq_weighted_sq_succ m

/-- **Second moment via `Nat.centralBinom`.** Packages `sum_sq_weighted_sq_succ`
    using Mathlib's central binomial coefficient: the second moment of row
    `m + 1` is `(m+1)²` times the central binomial coefficient of row `m`. -/
theorem sum_sq_weighted_centralBinom (m : ℕ) :
    ∑ k ∈ range (m + 2), k ^ 2 * ((m + 1).choose k) ^ 2
      = (m + 1) ^ 2 * Nat.centralBinom m := by
  rw [sum_sq_weighted_sq_succ, Nat.centralBinom]

/-- Sanity check: `∑_{k=0}^{3} k²·C(3,k)² = 0 + 9 + 4·9 + 9·1 = 54 = 9·C(4,2) = 9·6`. -/
example : ∑ k ∈ range 4, k ^ 2 * ((3 : ℕ).choose k) ^ 2 = 54 := by decide

/-- Sanity check of the closed form at `n = 3`: `54 = 3² · C(4, 2)`. -/
example : ∑ k ∈ range 4, k ^ 2 * ((3 : ℕ).choose k) ^ 2
    = 3 ^ 2 * (2 * 3 - 2).choose (3 - 1) := by decide

end CombinationsFormulaOQ07OQ04
