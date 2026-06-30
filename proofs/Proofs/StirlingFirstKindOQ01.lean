/-
Stirling Numbers of the First Kind: the row sum  ∑ₖ c(n,k) = n!

Source: Open question from the stirling-first-kind gallery family
Status: VERIFIED (0 axioms, 0 sorries)

`Nat.stirlingFirst n k` is the unsigned Stirling number of the first kind: the
number of permutations of an `n`-element set having exactly `k` disjoint cycles.
Mathlib (`Mathlib/Combinatorics/Enumerative/Stirling.lean`) provides the defining
recurrence together with several boundary/edge values:

  c(n+1, k+1) = n·c(n, k+1) + c(n, k)     (`stirlingFirst_succ_succ`)
  c(n, n)     = 1                          (`stirlingFirst_self`)
  c(n+1, 1)   = n!                         (`stirlingFirst_one_right`,  the single n-cycle)
  c(n+1, n)   = C(n+1, 2)                  (`stirlingFirst_succ_self_left`)
  c(n, k)     = 0   for n < k              (`stirlingFirst_eq_zero_of_lt`)

but it does NOT record the classical *row sum* identity

      ∑_{k=0}^{n} c(n, k) = n!.

Combinatorially this is immediate: every permutation of an `n`-set has *some*
number of cycles, so summing the cycle-count statistic over all `k` recovers the
total number of permutations, `n!`. We fill that gap with a purely arithmetic
proof from the recurrence.

The recurrence collapses the row sum to the factorial recursion. Writing
`R n = ∑_{k ≤ n} c(n, k)`, the rule c(n+1,k+1) = n·c(n,k+1) + c(n,k) gives

      R(n+1) = n·A + R(n),   where  A = ∑_{k ≤ n} c(n, k+1),

and a one-step shift of the summation index shows `A + c(n,0) = R(n)`. Since
`n·c(n,0) = 0` for every `n` (c(n,0) = 0 unless n = 0, in which case the factor n
is 0), this yields `n·A = n·R(n)` and hence the clean factorial recursion

      R(n+1) = n·R(n) + R(n) = (n+1)·R(n).

With `R(0) = c(0,0) = 1 = 0!`, induction gives `R(n) = n!`.

We prove:
1. `stirlingFirst_zero_left`  — the edge value c(n,0) = 0 for n ≥ 1, and n·c(n,0) = 0 for all n
2. `stirlingFirst_row_sum`    — the row sum identity ∑_{k ≤ n} c(n,k) = n!
3. `stirlingFirst_row_sum_pos`— the row sum is positive (there is always a permutation)
-/

import Mathlib

open Nat Finset

namespace StirlingFirstKindOQ01

/-- The full leftmost column vanishes except at the apex: `n · c(n,0) = 0` for every `n`.
For `n = 0` the prefactor kills it; for `n ≥ 1`, `c(n,0) = 0` itself
(`stirlingFirst_succ_zero`). This is the fact that makes the row-sum recursion
collapse exactly to the factorial recursion. -/
theorem stirlingFirst_mul_zero_left (n : ℕ) : n * Nat.stirlingFirst n 0 = 0 := by
  cases n with
  | zero => simp
  | succ m => simp [Nat.stirlingFirst_succ_zero]

/-- **Row sum of the Stirling numbers of the first kind.**
Summing the cycle-count statistic over all possible cycle numbers `k` recovers the
total number of permutations of an `n`-element set:

  ∑_{k = 0}^{n} c(n, k) = n!.

Proof by induction on `n`, using the Mathlib recurrence
`c(n+1, k+1) = n·c(n, k+1) + c(n, k)` and an index shift. -/
theorem stirlingFirst_row_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n ! := by
  induction n with
  | zero => decide
  | succ n ih =>
      -- Peel off the `k = 0` term (which is 0) using `sum_range_succ'`.
      rw [Finset.sum_range_succ' (fun k => Nat.stirlingFirst (n + 1) k) (n + 1)]
      rw [Nat.stirlingFirst_succ_zero, add_zero]
      -- Apply the recurrence termwise and split the sum.
      have hrec : ∀ k ∈ Finset.range (n + 1),
          Nat.stirlingFirst (n + 1) (k + 1)
            = n * Nat.stirlingFirst n (k + 1) + Nat.stirlingFirst n k := by
        intro k _
        rw [Nat.stirlingFirst_succ_succ]
      rw [Finset.sum_congr rfl hrec, Finset.sum_add_distrib, ← Finset.mul_sum]
      -- Name the two pieces.
      set A := ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n (k + 1) with hA_def
      -- The bare row sum `R n` equals `n !` by the induction hypothesis.
      -- The shifted sum `A` satisfies `A + c(n,0) = R n`.
      have hshift : A + Nat.stirlingFirst n 0 = ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k := by
        rw [hA_def]
        -- `A = ∑_{k<n} c(n,k+1) + c(n,n+1)` (top term vanishes), and
        -- `∑_{k<n} c(n,k+1) + c(n,0) = R n` is exactly `sum_range_succ'`.
        rw [Finset.sum_range_succ (fun k => Nat.stirlingFirst n (k + 1)) n,
          Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), add_zero]
        rw [Finset.sum_range_succ' (fun k => Nat.stirlingFirst n k) n]
      -- Conclude: `n·A = n·R n` since `n·c(n,0) = 0`, then fold the factorial recursion.
      have hnA : n * A = n * (n !) := by
        have : n * (A + Nat.stirlingFirst n 0) = n * (n !) := by rw [hshift, ih]
        rw [Nat.mul_add, stirlingFirst_mul_zero_left, add_zero] at this
        exact this
      rw [hnA, ih, Nat.factorial_succ]
      ring

/-- The row sum is strictly positive: every set admits at least one permutation. -/
theorem stirlingFirst_row_sum_pos (n : ℕ) :
    0 < ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k := by
  rw [stirlingFirst_row_sum]
  exact Nat.factorial_pos n

/-- Concrete check: the fourth row sums to `4! = 24`. -/
example : ∑ k ∈ Finset.range 5, Nat.stirlingFirst 4 k = 24 := by decide

/-- Concrete value: there are 11 permutations of a 4-set with exactly 2 cycles. -/
example : Nat.stirlingFirst 4 2 = 11 := by decide

end StirlingFirstKindOQ01
