import Mathlib

/-
# The Diagonal of Vandermonde: Self-Convolution of a Binomial Row

## Open Question OQ-10

The **general** Vandermonde convolution
`C(m+n, r) = ∑_{k=0}^{r} C(m,k) · C(n, r-k)`
is already in the gallery (`CombinationsFormulaOQ01.vandermonde`), as are its
hypergeometric / Chu–Vandermonde polynomial generalizations (OQ-01-OQ-02).

This file proves the most celebrated *specialization* of Vandermonde — the
**diagonal**, obtained by setting `m = n` and exploiting the symmetry
`C(n, n-k) = C(n, k)`.  The headline consequence,

        ∑_{k=0}^{n} C(n,k)² = C(2n, n),

(the sum of the squares of a row of Pascal's triangle is the central binomial
coefficient) is a classical identity that does *not* appear elsewhere in the
gallery, where only the bound `C(2n,n) ≤ 4ⁿ` and the log-concavity of a row
(OQ-04) are recorded.

## Results

1. `sum_choose_mul_choose_shift` — the **shifted diagonal**: for `d ≤ n`,

        ∑_{k=0}^{n-d} C(n,k) · C(n, k+d) = C(2n, n+d).

   Combinatorially: to choose `n+d` people from two groups of `n`, pick `k`
   from the first group and the rest from the second; pairing each choice with
   its mirror gives the self-convolution.

2. `sum_sq_choose` — the **sum-of-squares** identity, the `d = 0` case:

        ∑_{k=0}^{n} C(n,k)² = C(2n, n).

## Method

Specialize Mathlib's Vandermonde `Nat.add_choose_eq` at `m = n`, evaluated at
`r = n - d`, and rewrite the inner coefficient `C(n, (n-d)-k)` to `C(n, k+d)`
via `Nat.choose_symm_of_eq_add` (using `n = ((n-d)-k) + (k+d)`).  The left side
`C(2n, n-d)` is rewritten to `C(2n, n+d)` by the same symmetry.  Everything
stays in ℕ with no truncated-subtraction pitfalls because every subtraction is
discharged by `omega` under the hypothesis `d ≤ n`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ10

open Nat Finset

/-- **Shifted diagonal of Vandermonde.**  For `d ≤ n`,

        ∑_{k=0}^{n-d} C(n,k) · C(n, k+d) = C(2n, n+d).

The self-convolution of a binomial row with a horizontal shift `d`.  Proved by
specializing Vandermonde's convolution at `m = n`, `r = n - d`, and folding the
inner coefficient back with the symmetry `C(n, (n-d)-k) = C(n, k+d)`. -/
theorem sum_choose_mul_choose_shift (n d : ℕ) (hd : d ≤ n) :
    ∑ k ∈ range (n - d + 1), n.choose k * n.choose (k + d)
      = (2 * n).choose (n + d) := by
  -- Vandermonde with both rows `n`, evaluated at `r = n - d`.
  have hv : (n + n).choose (n - d)
      = ∑ k ∈ range (n - d + 1), n.choose k * n.choose ((n - d) - k) := by
    rw [Nat.add_choose_eq]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => n.choose i * n.choose j) (n - d)
  -- Rewrite the inner coefficient `C(n, (n-d)-k)` to `C(n, k+d)`.
  have hsum : ∑ k ∈ range (n - d + 1), n.choose k * n.choose (k + d)
      = (n + n).choose (n - d) := by
    rw [hv]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hsplit : n = ((n - d) - k) + (k + d) := by omega
    rw [(Nat.choose_symm_of_eq_add hsplit).symm]
  rw [hsum, two_mul]
  -- `C(2n, n-d) = C(2n, n+d)` by symmetry.
  exact Nat.choose_symm_of_eq_add (by omega)

/-- **Sum of squares of a binomial row** (the `d = 0` diagonal):

        ∑_{k=0}^{n} C(n,k)² = C(2n, n).

The sum of the squares of the entries in row `n` of Pascal's triangle equals the
central binomial coefficient `C(2n, n)`. -/
theorem sum_sq_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k) ^ 2 = (2 * n).choose n := by
  have h := sum_choose_mul_choose_shift n 0 (Nat.zero_le n)
  simpa [sq] using h

-- Concrete verifications (axiom-free `decide`).
example : ∑ k ∈ range 4, (Nat.choose 3 k) ^ 2 = Nat.choose 6 3 := by decide
example : ∑ k ∈ range 5, (Nat.choose 4 k) ^ 2 = Nat.choose 8 4 := by decide
example : ∑ k ∈ range 3, Nat.choose 4 k * Nat.choose 4 (k + 2)
    = Nat.choose 8 6 := by decide

end CombinationsFormulaOQ10
