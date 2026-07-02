import Mathlib

/-
# The Weighted Diagonal of Vandermonde: a Closed Form for ∑ k·C(n,k)²

## Open Question OQ-10-OQ-01

The parent file (`CombinationsFormulaOQ10`) proves the **unweighted** diagonal
of Vandermonde, the sum of the squares of a Pascal row,

        ∑_{k=0}^{n} C(n,k)² = C(2n, n).

This file proves the **first-moment** (weighted) refinement, the closed form

        ∑_{k=0}^{n} k · C(n,k)² = n · C(2n-1, n-1),

which the parent's open questions ask for.  The right-hand side is the standard
"weighted central binomial": the number of ways to pick a committee of `n` from
`2n-1` people together with a designated chair among a distinguished half.

## Method

The engine is the **absorption identity**
`(k+1)·C(n+1,k+1) = (n+1)·C(n,k)` (Mathlib's `Nat.succ_mul_choose_eq`),
which turns the weight `k` into a shift of the binomial row.  Writing every
subtraction-free statement over `n+1`:

1. Peel the vanishing `k = 0` term with `Finset.sum_range_succ'` and reindex to
   `∑_{j=0}^{n} (j+1)·C(n+1,j+1)²`.
2. Apply absorption to one factor: each term becomes
   `(n+1)·C(n,j)·C(n+1,j+1)`, so `(n+1)` factors out of the whole sum.
3. The residual sum `∑_{j=0}^{n} C(n,j)·C(n+1,j+1)` is a genuine (unequal-row)
   Vandermonde convolution; folding `C(n+1,j+1) = C(n+1,n-j)` by symmetry and
   applying `Nat.add_choose_eq` collapses it to `C(2n+1, n)`.

Everything is proved over `ℕ` with no truncated-subtraction pitfalls; the
`n·C(2n-1,n-1)` form is recovered from the `n+1` form by `omega` arithmetic on
the indices.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ10OQ01

open Nat Finset

/-- **Unequal-row Vandermonde convolution** feeding the weighted diagonal:

        ∑_{j=0}^{n} C(n,j) · C(n+1, j+1) = C(2n+1, n).

Rows `n` and `n+1` are convolved; folding `C(n+1,j+1) = C(n+1,n-j)` by symmetry
reduces this to `Nat.add_choose_eq` at `m = n`, `n' = n+1`, `r = n`. -/
theorem sum_choose_mul_choose_succ_shift (n : ℕ) :
    ∑ j ∈ range (n + 1), n.choose j * (n + 1).choose (j + 1)
      = (2 * n + 1).choose n := by
  -- Vandermonde with rows `n` and `n+1`, evaluated at `r = n`.
  have hv : (n + (n + 1)).choose n
      = ∑ j ∈ range (n + 1), n.choose j * (n + 1).choose (n - j) := by
    rw [Nat.add_choose_eq]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => n.choose i * (n + 1).choose j) n
  -- Fold the inner coefficient `C(n+1, n-j)` back to `C(n+1, j+1)`.
  have hsum : ∑ j ∈ range (n + 1), n.choose j * (n + 1).choose (j + 1)
      = (n + (n + 1)).choose n := by
    rw [hv]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hsplit : n + 1 = (j + 1) + (n - j) := by omega
    rw [Nat.choose_symm_of_eq_add hsplit]
  rw [hsum]
  congr 1
  omega

/-- **Weighted diagonal, subtraction-free form.**

        ∑_{k=0}^{n+1} k · C(n+1,k)² = (n+1) · C(2n+1, n).

The `k = 0` term vanishes; absorption `(k)·C(n+1,k) = (n+1)·C(n,k-1)` converts
each remaining term into `(n+1)·C(n,j)·C(n+1,j+1)`, and the residual convolution
collapses via `sum_choose_mul_choose_succ_shift`. -/
theorem sum_weighted_sq_choose_succ (n : ℕ) :
    ∑ k ∈ range (n + 2), k * ((n + 1).choose k) ^ 2
      = (n + 1) * (2 * n + 1).choose n := by
  -- Peel the vanishing `k = 0` term and reindex `k = j + 1`.
  rw [Finset.sum_range_succ' (fun k => k * ((n + 1).choose k) ^ 2) (n + 1)]
  simp only [Nat.zero_mul, add_zero]
  -- Each term: `(j+1)·C(n+1,j+1)² = (n+1)·(C(n,j)·C(n+1,j+1))`.
  have hterm : ∀ j ∈ range (n + 1),
      (j + 1) * ((n + 1).choose (j + 1)) ^ 2
        = (n + 1) * (n.choose j * (n + 1).choose (j + 1)) := by
    intro j _
    have habsorb : (n + 1) * n.choose j = (n + 1).choose (j + 1) * (j + 1) :=
      Nat.add_one_mul_choose_eq n j
    have : (j + 1) * (n + 1).choose (j + 1) = (n + 1) * n.choose j := by
      rw [habsorb]; ring
    calc (j + 1) * ((n + 1).choose (j + 1)) ^ 2
        = ((j + 1) * (n + 1).choose (j + 1)) * (n + 1).choose (j + 1) := by ring
      _ = ((n + 1) * n.choose j) * (n + 1).choose (j + 1) := by rw [this]
      _ = (n + 1) * (n.choose j * (n + 1).choose (j + 1)) := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_choose_mul_choose_succ_shift]

/-- **Weighted diagonal of Vandermonde** (the headline closed form):

        ∑_{k=0}^{n} k · C(n,k)² = n · C(2n-1, n-1).

The first-moment refinement of `∑ C(n,k)² = C(2n,n)`.  Recovered from the
subtraction-free `sum_weighted_sq_choose_succ` by `omega` arithmetic on the
indices; the `n = 0` degenerate case (both sides `0`) is handled uniformly. -/
theorem sum_weighted_sq_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * (n.choose k) ^ 2
      = n * (2 * n - 1).choose (n - 1) := by
  cases n with
  | zero => decide
  | succ m =>
      have h := sum_weighted_sq_choose_succ m
      -- `2*(m+1)-1 = 2*m+1` and `(m+1)-1 = m`.
      have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have e2 : (m + 1) - 1 = m := by omega
      rw [e1, e2]
      simpa using h

-- Concrete verifications (axiom-free `decide`).
-- ∑ k·C(3,k)² = 1·9 + 2·9 + 3·1 = 9+18+3 = 30 = 3·C(5,2) = 3·10.
example : ∑ k ∈ range 4, k * (Nat.choose 3 k) ^ 2 = 3 * Nat.choose 5 2 := by decide
-- ∑ k·C(4,k)² = 4·C(7,3) = 4·35 = 140.
example : ∑ k ∈ range 5, k * (Nat.choose 4 k) ^ 2 = 4 * Nat.choose 7 3 := by decide
-- ∑ k·C(5,k)² = 5·C(9,4) = 5·126 = 630.
example : ∑ k ∈ range 6, k * (Nat.choose 5 k) ^ 2 = 5 * Nat.choose 9 4 := by decide

end CombinationsFormulaOQ10OQ01
