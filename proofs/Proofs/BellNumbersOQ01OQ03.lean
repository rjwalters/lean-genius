/-
# The row sum of the unsigned Stirling numbers of the first kind is `n!`

The unsigned Stirling number of the first kind `c(n, k) = Nat.stirlingFirst n k`
counts the permutations of an `n`-element set having exactly `k` disjoint cycles.
Conditioning on the number of cycles partitions *all* permutations of an
`n`-element set, so grouping the `n!` permutations by their cycle count gives the
classical "companion" identity to the Bell / second-kind row sum
(`bell-numbers-oq-01`):

    Σ_{k=0}^{n} c(n, k) = n!.

Pinned Mathlib carries `Nat.stirlingFirst` with its triangular recurrence
`c(n+1, k+1) = n·c(n, k+1) + c(n, k)` and a handful of boundary values
(`stirlingFirst_self`, `stirlingFirst_one_right`, `stirlingFirst_succ_self_left`),
but it does **not** record that the rows sum to the factorial.  This file fills
that gap and connects the arithmetic identity to the actual count of permutations.

The proof is a direct induction on `n` using only the triangular recurrence.  The
`(n+1)`-st row sum splits, via `c(n+1, k+1) = n·c(n, k+1) + c(n, k)`, into
`n·(Σ_k c(n, k+1)) + (Σ_k c(n, k))`.  Re-indexing turns the first inner sum back
into the `n`-th row sum — the `k = 0` boundary term `c(n, 0)` that the shift drops
is killed by the factor `n` (`n·c(n, 0) = 0` for all `n`) — so the recurrence
collapses to `(n+1)·n! = (n+1)!`.

## Main results (0 sorry, 0 axiom)
* `mul_stirlingFirst_zero`      — `n · c(n, 0) = 0`.
* `stirlingFirst_row_sum`       — `Σ_{k≤n} c(n, k) = n!`.
* `stirlingFirst_row_sum_eq_card_perm` — `Σ_{k≤n} c(n, k) = card (Perm (Fin n))`.

Fully machine-checked, no extra axioms, no `native_decide`.
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace BellNumbersOQ01OQ03

open Finset Nat

/-- `n · c(n, 0) = 0`: the zeroth unsigned Stirling number of the first kind is `1`
at `n = 0` (where the factor `n` kills the product) and `0` for every `n ≥ 1`. -/
theorem mul_stirlingFirst_zero (n : ℕ) : n * Nat.stirlingFirst n 0 = 0 := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.stirlingFirst_succ_zero]

/-- **Row sum of the unsigned Stirling numbers of the first kind.**
`Σ_{k=0}^{n} c(n, k) = n!`.  Summing the number of `n`-permutations with exactly
`k` cycles over all `k` recovers the total number `n!` of permutations.  Absent
from pinned Mathlib, which records only boundary values of `stirlingFirst`. -/
theorem stirlingFirst_row_sum (n : ℕ) :
    ∑ k ∈ range (n + 1), Nat.stirlingFirst n k = n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Peel the `k = 0` term (which vanishes) and expand each `c(n+1, i+1)` by the
    -- triangular recurrence `c(n+1, i+1) = n·c(n, i+1) + c(n, i)`.
    rw [Finset.sum_range_succ' (fun k => Nat.stirlingFirst (n + 1) k) (n + 1)]
    simp only [Nat.stirlingFirst_succ_zero, add_zero, Nat.stirlingFirst_succ_succ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    -- Goal: `n · (Σ_{i≤n} c(n, i+1)) + (Σ_{i≤n} c(n, i)) = (n+1)!`.
    -- The second sum is the induction hypothesis.
    rw [ih]
    -- Re-index the first inner sum: `c(n,0) + Σ_{i≤n} c(n, i+1) = Σ_{k≤n+1} c(n,k) = n!`.
    have hsplit :
        (∑ i ∈ range (n + 1), Nat.stirlingFirst n (i + 1)) + Nat.stirlingFirst n 0 = n ! := by
      have h2 : ∑ k ∈ range (n + 1 + 1), Nat.stirlingFirst n k = n ! := by
        rw [Finset.sum_range_succ (fun k => Nat.stirlingFirst n k) (n + 1),
          Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), add_zero, ih]
      rwa [Finset.sum_range_succ' (fun k => Nat.stirlingFirst n k) (n + 1)] at h2
    -- Multiply `hsplit` by `n`; the boundary term `n·c(n,0)` vanishes.
    have hnB : n * (∑ i ∈ range (n + 1), Nat.stirlingFirst n (i + 1)) = n * n ! := by
      have h : n * ((∑ i ∈ range (n + 1), Nat.stirlingFirst n (i + 1)) + Nat.stirlingFirst n 0)
          = n * n ! := by rw [hsplit]
      rwa [Nat.mul_add, mul_stirlingFirst_zero, add_zero] at h
    rw [hnB, Nat.factorial_succ]
    ring

/-- **The Stirling first-kind row sum equals the number of permutations.**
`Σ_{k=0}^{n} c(n, k) = |Perm (Fin n)|`.  This is the combinatorial content of
`stirlingFirst_row_sum`: the left side sorts the permutations of `Fin n` by their
cycle count, and the right side counts them all at once. -/
theorem stirlingFirst_row_sum_eq_card_perm (n : ℕ) :
    ∑ k ∈ range (n + 1), Nat.stirlingFirst n k = Fintype.card (Equiv.Perm (Fin n)) := by
  rw [stirlingFirst_row_sum, Fintype.card_perm, Fintype.card_fin]

end BellNumbersOQ01OQ03
