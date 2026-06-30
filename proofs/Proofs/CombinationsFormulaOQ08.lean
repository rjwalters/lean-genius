import Mathlib

/-
# Fibonacci Numbers as Sums Along the Shallow Diagonals of Pascal's Triangle

## Open Question OQ-08

The Fibonacci numbers are the sums of the binomial coefficients lying along the
"shallow diagonals" of Pascal's triangle:

  fib (n + 1) = C(n,0) + C(n-1,1) + C(n-2,2) + ⋯

Mathlib already provides this identity in its *antidiagonal* form,
`Nat.fib_succ_eq_sum_choose`:

  fib (n + 1) = ∑ p ∈ antidiagonal n, choose p.1 p.2 .

The antidiagonal `{(i, j) : i + j = n}` is not the textbook presentation, and the
visible "diagonal" indexing is hidden inside the pair structure.  The contribution
of this file is to reindex that sum into the two presentations one actually meets
in combinatorics texts:

1. `fib_eq_sum_range_choose`  — a single sum over `Finset.range (n + 1)`:
        fib (n + 1) = ∑ k < n+1, C(n - k, k).
   This is the literal "shallow diagonal" formula: the k-th term `C(n-k, k)` is the
   entry that sits k steps up the diagonal.

2. `fib_eq_sum_range_half_choose` — the same sum truncated to its genuinely nonzero
   range `0 ≤ k ≤ ⌊n/2⌋`:
        fib (n + 1) = ∑ k < n/2 + 1, C(n - k, k),
   reflecting that `C(n - k, k) = 0` once `k` overshoots `n/2`.

## Mathematical Context

A shallow diagonal of Pascal's triangle collects entries `C(n, 0), C(n-1, 1), …`,
stepping one row up and one column right at each step.  The classical theorem
(due to Lucas) states their sum is a Fibonacci number.  The proof reduces to the
antidiagonal identity by:

* `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, which evaluates the antidiagonal
  pair `(i, j)` as `(k, n - k)` over `k ∈ range (n+1)`, and
* `Finset.sum_range_reflect`, which reverses the index `k ↦ n - k` so that the
  surviving summand becomes the textbook `C(n - k, k)`.

The truncation step uses `Finset.sum_subset` together with
`Nat.choose_eq_zero_of_lt`: when `k > n/2` we have `n - k < k`, so `C(n - k, k) = 0`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ08

open Finset

/-- **Anchor (Mathlib form).** Fibonacci as a sum over the antidiagonal of `n`.
    This is exactly `Nat.fib_succ_eq_sum_choose`, restated here as the starting
    point for the reindexed diagonal presentations below. -/
theorem fib_eq_sum_antidiagonal_choose (n : ℕ) :
    Nat.fib (n + 1) = ∑ p ∈ Finset.antidiagonal n, Nat.choose p.1 p.2 :=
  Nat.fib_succ_eq_sum_choose n

/-- **Shallow-diagonal formula (range form).**
    `fib (n + 1) = ∑_{k=0}^{n} C(n - k, k)` — the textbook sum along the shallow
    diagonal of Pascal's triangle. -/
theorem fib_eq_sum_range_choose (n : ℕ) :
    Nat.fib (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) k := by
  rw [fib_eq_sum_antidiagonal_choose,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose i j) n,
      ← Finset.sum_range_reflect (fun k => Nat.choose (n - k) k) (n + 1)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk]

/-- The shallow-diagonal terms vanish past the midpoint: for `k > n / 2` we have
    `n - k < k`, hence `C(n - k, k) = 0`. -/
theorem choose_shallow_eq_zero {n k : ℕ} (hk : n / 2 < k) :
    Nat.choose (n - k) k = 0 := by
  -- `omega` understands `n / 2` (division by the literal `2`): `n / 2 < k ⟹ n - k < k`.
  exact Nat.choose_eq_zero_of_lt (by omega)

/-- **Truncated shallow-diagonal formula.**
    `fib (n + 1) = ∑_{k=0}^{⌊n/2⌋} C(n - k, k)` — the sum restricted to the range
    where the binomial coefficients are nonzero. -/
theorem fib_eq_sum_range_half_choose (n : ℕ) :
    Nat.fib (n + 1) = ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k := by
  rw [fib_eq_sum_range_choose]
  symm
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro k _ hk
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hk
    exact choose_shallow_eq_zero hk

/-- Sanity check: `fib 6 = 8` recovered from the shallow-diagonal sum
    `C(5,0) + C(4,1) + C(3,2) = 1 + 4 + 3 = 8`. -/
example : Nat.fib 6 = 8 := by
  rw [fib_eq_sum_range_half_choose 5]
  decide

end CombinationsFormulaOQ08
