import Mathlib

/-
# Vandermonde's Convolution and the Central Binomial Sum-of-Squares

## Open Question OQ-07

Vandermonde's convolution identity states

  C(m + n, k) = ∑_{i+j=k} C(m, i) · C(n, j) .

Mathlib provides this in its *antidiagonal* form, `Nat.add_choose_eq`:

  (m + n).choose k = ∑ p ∈ antidiagonal k, m.choose p.1 * n.choose p.2 .

This file reindexes that identity into the single-sum form one usually writes,
and draws out the most famous special case.

1. `add_choose_eq_sum_range` — the range form:
        C(m + n, k) = ∑_{i=0}^{k} C(m, i) · C(n, k - i).

2. `central_binom_eq_sum_sq` — specializing `m = n`, `k = n` and using the
   symmetry `C(n, n-i) = C(n, i)` collapses the convolution into a sum of
   squares:
        C(2n, n) = ∑_{i=0}^{n} C(n, i)² .

## Mathematical Context

Vandermonde's identity counts the ways to choose `k` objects from a pile of
`m + n` by splitting according to how many come from the first `m`.  Its
diagonal (single-sum) presentation is the form that appears in generating-
function manipulations and in Gould's tables of binomial identities.  The
central case `C(2n, n) = ∑ C(n, i)²` says: the number of lattice paths to the
center of Pascal's triangle equals the sum of squares of the entries in row
`n` — a cornerstone identity in enumerative combinatorics.

The proofs reduce to Mathlib's `Nat.add_choose_eq` via
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ` (which evaluates the
antidiagonal pair `(i, j)` as `(i, k - i)` over `i ∈ range (k+1)`), and, for the
central case, `Nat.choose_symm` (`C(n, n-i) = C(n, i)` for `i ≤ n`).

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ07

open Finset

/-- **Anchor (Mathlib form).** Vandermonde's convolution over the antidiagonal.
    This is exactly `Nat.add_choose_eq`, restated as the starting point. -/
theorem add_choose_eq_antidiagonal (m n k : ℕ) :
    (m + n).choose k = ∑ p ∈ Finset.antidiagonal k, m.choose p.1 * n.choose p.2 :=
  Nat.add_choose_eq m n k

/-- **Vandermonde's convolution (range form).**
    `C(m + n, k) = ∑_{i=0}^{k} C(m, i) · C(n, k - i)`. -/
theorem add_choose_eq_sum_range (m n k : ℕ) :
    (m + n).choose k = ∑ i ∈ Finset.range (k + 1), m.choose i * n.choose (k - i) := by
  rw [add_choose_eq_antidiagonal,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => m.choose i * n.choose j) k]

/-- **Central binomial coefficient as a sum of squares.**
    `C(2n, n) = ∑_{i=0}^{n} C(n, i)²` — the diagonal of Vandermonde's identity. -/
theorem central_binom_eq_sum_sq (n : ℕ) :
    (2 * n).choose n = ∑ i ∈ Finset.range (n + 1), (n.choose i) ^ 2 := by
  rw [two_mul, add_choose_eq_sum_range]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [Nat.choose_symm hi, sq]

/-- Sanity check: `C(6, 3) = 20` recovered from `∑ C(3,i)² = 1 + 9 + 9 + 1`. -/
example : (2 * 3).choose 3 = 20 := by
  rw [central_binom_eq_sum_sq 3]
  decide

end CombinationsFormulaOQ07
