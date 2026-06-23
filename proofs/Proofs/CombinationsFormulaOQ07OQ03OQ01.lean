import Mathlib
import Proofs.CombinationsFormulaOQ07

/-
# The Second Moment of Squared Binomial Coefficients

## Open Question OQ-07-OQ-03-OQ-01

The parent file OQ-07-OQ-03 computes the *first* moment of the squared Pascal
row, `∑_{k} k · C(n, k)² = n · C(2n − 1, n − 1)`.  This file computes the
*second* moment:

  ∑_{k=0}^{n} k² · C(n, k)² = n² · C(2n − 2, n − 1).                  (★)

For example, at `n = 3` the left side is `0 + 1·9 + 4·9 + 9·1 = 54`, and the
right side is `9 · C(4, 2) = 9 · 6 = 54`.

## The single-absorption proof

The first-moment identity needed the reflection symmetry `k ↦ n − k`.  The
second moment instead falls out of a *single* application of the absorption
identity

  (k + 1) · C(n + 1, k + 1) = (n + 1) · C(n, k)        (`Nat.succ_mul_choose_eq`),

with no induction, generating functions, or factorial bookkeeping.

Write the second moment with `n = m + 1`.  Its `k = 0` term vanishes, so after
shifting `k = j + 1` the sum runs over `j ∈ {0, …, m}`:

  ∑_{k} k² · C(m+1, k)² = ∑_{j} (j + 1)² · C(m+1, j+1)² .

Squaring the absorption identity turns each summand into a `j`-free multiple of
a *single* binomial square:

  (j + 1)² · C(m+1, j+1)² = ((j+1)·C(m+1,j+1))² = ((m+1)·C(m,j))²
                          = (m + 1)² · C(m, j)² .

Factoring out `(m + 1)²` leaves exactly the unweighted sum of squares of the
`m`-th Pascal row, which the parent OQ-07 identity `central_binom_eq_sum_sq`
evaluates to the central binomial coefficient:

  ∑_{j=0}^{m} C(m, j)² = C(2m, m).

Hence the second moment equals `(m + 1)² · C(2m, m)`, i.e. `n² · C(2n−2, n−1)`.

## Probabilistic reading

Reading `C(n, k)² / C(2n, n)` as the hypergeometric distribution on
`{0, …, n}`, the parent first moment says the mean is `n / 2`.  Identity (★)
gives the **raw second moment** `E[X²] = n² · C(2n−2, n−1) / C(2n, n)`.
Combining the two yields the variance of this hypergeometric law — the
fluctuation of the Vandermonde split of a `2n`-set into two halves.

## Results

1. `sum_sq_weighted_sq_succ` — the subtraction-free closed form
   `∑_{k=0}^{m+1} k² · C(m+1, k)² = (m+1)² · C(2m, m)`, the conceptual core.
2. `sum_sq_weighted_sq` — the classical form, for `n ≥ 1`,
   `∑_{k=0}^{n} k² · C(n, k)² = n² · C(2n − 2, n − 1)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ03OQ01

open Finset

/-- **Single-absorption term identity.**  Squaring
    `(j+1)·C(m+1,j+1) = (m+1)·C(m,j)` collapses the `j`-weighted binomial square
    to a `j`-free multiple of `C(m, j)²`. -/
theorem term_absorb (m j : ℕ) :
    (j + 1) ^ 2 * ((m + 1).choose (j + 1)) ^ 2
      = (m + 1) ^ 2 * (m.choose j) ^ 2 := by
  -- `key : (m+1) · C(m,j) = C(m+1,j+1) · (j+1)`
  have key : (m + 1) * m.choose j = (m + 1).choose (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq m j
  have h : (j + 1) * (m + 1).choose (j + 1) = (m + 1) * m.choose j := by
    rw [key]; ring
  calc (j + 1) ^ 2 * ((m + 1).choose (j + 1)) ^ 2
      = ((j + 1) * (m + 1).choose (j + 1)) ^ 2 := by rw [mul_pow]
    _ = ((m + 1) * m.choose j) ^ 2 := by rw [h]
    _ = (m + 1) ^ 2 * (m.choose j) ^ 2 := by rw [mul_pow]

/-- **Second moment (subtraction-free form).**
    `∑_{k=0}^{m+1} k² · C(m+1, k)² = (m+1)² · C(2m, m)`.
    Writing the moment with `n = m + 1` keeps the statement free of
    natural-number subtraction. -/
theorem sum_sq_weighted_sq_succ (m : ℕ) :
    ∑ k ∈ range (m + 2), k ^ 2 * ((m + 1).choose k) ^ 2
      = (m + 1) ^ 2 * (2 * m).choose m := by
  -- Peel the `k = 0` term (which vanishes: `0² · C(m+1,0)² = 0`) and reindex by `j+1`.
  have reindex :
      ∑ k ∈ range (m + 2), k ^ 2 * ((m + 1).choose k) ^ 2
        = ∑ j ∈ range (m + 1), (j + 1) ^ 2 * ((m + 1).choose (j + 1)) ^ 2 := by
    rw [Finset.sum_range_succ' (fun k => k ^ 2 * ((m + 1).choose k) ^ 2) (m + 1)]
    simp
  rw [reindex]
  calc ∑ j ∈ range (m + 1), (j + 1) ^ 2 * ((m + 1).choose (j + 1)) ^ 2
      = ∑ j ∈ range (m + 1), (m + 1) ^ 2 * (m.choose j) ^ 2 :=
        Finset.sum_congr rfl (fun j _ => term_absorb m j)
    _ = (m + 1) ^ 2 * ∑ j ∈ range (m + 1), (m.choose j) ^ 2 := by rw [Finset.mul_sum]
    _ = (m + 1) ^ 2 * (2 * m).choose m := by
        rw [← CombinationsFormulaOQ07.central_binom_eq_sum_sq]

/-- **Second moment (classical form).**  For `n ≥ 1`,
    `∑_{k=0}^{n} k² · C(n, k)² = n² · C(2n − 2, n − 1)`. -/
theorem sum_sq_weighted_sq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), k ^ 2 * (n.choose k) ^ 2 = n ^ 2 * (2 * n - 2).choose (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1, e2]
  exact sum_sq_weighted_sq_succ m

/-- Sanity check: `∑_{k=0}^{3} k²·C(3,k)² = 0 + 9 + 36 + 9 = 54 = 3²·C(4,2) = 9·6`. -/
example : ∑ k ∈ range 4, k ^ 2 * ((3 : ℕ).choose k) ^ 2 = 54 := by decide

/-- Sanity check of the closed form at `n = 3`: `54 = 3² · C(4, 2)`. -/
example : ∑ k ∈ range 4, k ^ 2 * ((3 : ℕ).choose k) ^ 2 = 3 ^ 2 * (2 * 3 - 2).choose (3 - 1) := by
  decide

end CombinationsFormulaOQ07OQ03OQ01
