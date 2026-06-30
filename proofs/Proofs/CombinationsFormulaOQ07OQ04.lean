import Mathlib
import Proofs.CombinationsFormulaOQ07
import Proofs.CombinationsFormulaOQ07OQ01
import Proofs.CombinationsFormulaOQ07OQ03

/-
# The Second Moment of the Squares of Binomial Coefficients

## Open Question OQ-07-OQ-04

The central identity of OQ-07 sums the *squares* of a Pascal row,

  C(2n, n) = ∑_{k=0}^{n} C(n, k)² ,

and OQ-03 computed its first moment, `2 · ∑ k · C(n,k)² = n · C(2n, n)`.
This file computes the **second moment**, weighting each square by `k²`.
The closed form is again a single binomial coefficient:

  ∑_{k=0}^{n} k² · C(n, k)² = n² · C(2n − 2, n − 1).                 (★)

Equivalently, in terms of the central binomial coefficient itself,

  2 · (2n − 1) · ∑_{k=0}^{n} k² · C(n, k)² = n³ · C(2n, n).          (★★)

Mathlib provides the unweighted row sum (`Nat.sum_range_choose`) and the
central sum of squares (here `CombinationsFormulaOQ07.central_binom_eq_sum_sq`),
but **not** this second-moment identity.

## The absorption proof

Unlike the first moment — which fell out of the reflection symmetry
`k ↦ n − k` — the second moment is cleanest via **absorption**.  The
committee-chair identity (OQ-01, `mul_choose_eq`) reads

  k · C(n, k) = n · C(n − 1, k − 1)            (1 ≤ k ≤ n).

Squaring it term by term turns a `k²`-weighted square of `C(n, k)` into an
*unweighted* square of `C(n − 1, k − 1)`:

  k² · C(n, k)² = n² · C(n − 1, k − 1)² .

Summing over `k` (the `k = 0` term vanishes, and `k ↦ k − 1` reindexes the
range) collapses the right-hand side to the parent sum of squares:

  ∑_{k} k² · C(n, k)² = n² · ∑_{j} C(n − 1, j)² = n² · C(2(n − 1), n − 1),

the last step being exactly `central_binom_eq_sum_sq (n − 1)`.

The central-binomial form (★★) follows from (★) together with the binomial
recurrence `n · C(2n, n) = 2 · (2n − 1) · C(2n − 2, n − 1)`, itself a short
consequence of the halving `C(2n, n) = 2 · C(2n−1, n−1)` (OQ-03) and one more
absorption step on the top Pascal row.

## Mathematical Context

Reading `C(n, k)² / C(2n, n)` as the hypergeometric distribution on
`{0, …, n}`, OQ-03 found its mean to be `n / 2`.  Identity (★) supplies the raw
second moment `E[k²] = n³ / (2(2n − 1)) · C(2n,n) / C(2n,n)`-style ratio; together
they pin down the variance `n² / (4(2n − 1))` of that distribution — the spread
of a Vandermonde split of a `2n`-set into two halves.

## Results

1. `mul_sq_choose_sq` — the squared absorption identity
   `k² · C(n, k)² = n² · C(n − 1, k − 1)²` (for `1 ≤ k ≤ n`), the conceptual core.
2. `sum_sq_weighted_sq` — the closed form (★)
   `∑ k² · C(n,k)² = n² · C(2n − 2, n − 1)`.
3. `central_binom_recurrence` — the bridge
   `n · C(2n, n) = 2 · (2n − 1) · C(2n − 2, n − 1)`.
4. `two_mul_pred_mul_sum_sq` — the central-binomial form (★★)
   `2 · (2n − 1) · ∑ k² · C(n,k)² = n³ · C(2n, n)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07OQ04

open Finset

/-- **Squared absorption.** Squaring the committee-chair identity
    `k · C(n, k) = n · C(n − 1, k − 1)` (OQ-01) converts a `k²`-weighted square of
    `C(n, k)` into an unweighted square of `C(n − 1, k − 1)`. -/
theorem mul_sq_choose_sq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    k ^ 2 * (n.choose k) ^ 2 = n ^ 2 * ((n - 1).choose (k - 1)) ^ 2 := by
  have habs := CombinationsFormulaOQ07OQ01.mul_choose_eq hk hkn
  -- habs : k * n.choose k = n * (n - 1).choose (k - 1)
  have hsq : (k * n.choose k) ^ 2 = (n * (n - 1).choose (k - 1)) ^ 2 := by rw [habs]
  rwa [mul_pow, mul_pow] at hsq

/-- **Second moment of the squared binomial coefficients.**
    `∑_{k=0}^{n} k² · C(n, k)² = n² · C(2n − 2, n − 1)`.  The `k = 0` term
    vanishes, absorption rewrites each remaining term, and the parent sum of
    squares (`central_binom_eq_sum_sq`) closes the inner sum. -/
theorem sum_sq_weighted_sq (n : ℕ) :
    ∑ k ∈ range (n + 1), k ^ 2 * (n.choose k) ^ 2
      = n ^ 2 * (2 * (n - 1)).choose (n - 1) := by
  obtain _ | m := n
  · simp
  · -- n = m + 1
    rw [Finset.sum_range_succ']
    rw [show (0 : ℕ) ^ 2 * ((m + 1).choose 0) ^ 2 = 0 from by ring, add_zero,
        Nat.add_sub_cancel]
    have key : ∀ i ∈ range (m + 1),
        (i + 1) ^ 2 * ((m + 1).choose (i + 1)) ^ 2 = (m + 1) ^ 2 * (m.choose i) ^ 2 := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h := mul_sq_choose_sq (n := m + 1) (k := i + 1) (by omega) (by omega)
      rwa [Nat.add_sub_cancel, Nat.add_sub_cancel] at h
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum,
        ← CombinationsFormulaOQ07.central_binom_eq_sum_sq m]

/-- **Binomial recurrence for the central coefficient.** For `n ≥ 1`,
    `n · C(2n, n) = 2 · (2n − 1) · C(2n − 2, n − 1)`.  It combines the halving
    `C(2n, n) = 2 · C(2n−1, n−1)` (OQ-03) with one absorption step
    `n · C(2n−1, n) = (2n−1) · C(2n−2, n−1)` on the top Pascal row, the two
    central entries `C(2n−1, n−1) = C(2n−1, n)` being equal by symmetry. -/
theorem central_binom_recurrence (n : ℕ) (hn : 1 ≤ n) :
    n * (2 * n).choose n = 2 * (2 * n - 1) * (2 * (n - 1)).choose (n - 1) := by
  rw [CombinationsFormulaOQ07OQ03.central_binom_two_mul_pred n hn]
  -- goal: n * (2 * (2*n-1).choose (n-1)) = 2 * (2*n-1) * (2*(n-1)).choose (n-1)
  have hsymm : (2 * n - 1).choose (n - 1) = (2 * n - 1).choose n := by
    have h := Nat.choose_symm (show n ≤ 2 * n - 1 by omega)
    rwa [show 2 * n - 1 - n = n - 1 by omega] at h
  rw [hsymm]
  have habs := CombinationsFormulaOQ07OQ01.mul_choose_eq
    (n := 2 * n - 1) (k := n) (by omega) (by omega)
  -- habs : n * (2*n-1).choose n = (2*n-1) * ((2*n-1)-1).choose (n-1)
  rw [show 2 * n - 1 - 1 = 2 * (n - 1) by omega] at habs
  rw [show n * (2 * (2 * n - 1).choose n) = 2 * (n * (2 * n - 1).choose n) by ring, habs]
  ring

/-- **Second moment via the central binomial coefficient.** For `n ≥ 1`,
    `2 · (2n − 1) · ∑_{k=0}^{n} k² · C(n, k)² = n³ · C(2n, n)`.  This packages the
    closed form (★) through the binomial recurrence, mirroring OQ-03's
    first-moment form `2 · ∑ k · C(n,k)² = n · C(2n, n)`. -/
theorem two_mul_pred_mul_sum_sq (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * ∑ k ∈ range (n + 1), k ^ 2 * (n.choose k) ^ 2
      = n ^ 3 * (2 * n).choose n := by
  rw [sum_sq_weighted_sq]
  have hrec := central_binom_recurrence n hn
  calc 2 * (2 * n - 1) * (n ^ 2 * (2 * (n - 1)).choose (n - 1))
      = n ^ 2 * (2 * (2 * n - 1) * (2 * (n - 1)).choose (n - 1)) := by ring
    _ = n ^ 2 * (n * (2 * n).choose n) := by rw [← hrec]
    _ = n ^ 3 * (2 * n).choose n := by ring

/-- Sanity check: `∑_{k=0}^{3} k²·C(3,k)² = 0 + 9 + 36 + 9 = 54 = 9·C(4,2) = 9·6`. -/
example : ∑ k ∈ range 4, k ^ 2 * ((3 : ℕ).choose k) ^ 2 = 54 := by decide

/-- Sanity check of the closed form (★) at `n = 3`: `54 = 3² · C(4, 2)`. -/
example : ∑ k ∈ range 4, k ^ 2 * ((3 : ℕ).choose k) ^ 2
    = 3 ^ 2 * (2 * (3 - 1)).choose (3 - 1) := by decide

/-- Sanity check of the central-binomial form (★★) at `n = 3`:
    `2 · 5 · 54 = 540 = 27 · 20 = 3³ · C(6, 3)`. -/
example : 2 * (2 * 3 - 1) * (∑ k ∈ range 4, k ^ 2 * ((3 : ℕ).choose k) ^ 2)
    = 3 ^ 3 * (2 * 3).choose 3 := by decide

end CombinationsFormulaOQ07OQ04
