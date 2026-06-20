/-
# Bell numbers as the row-sum of the Stirling numbers of the second kind

The Bell number `Bₙ` counts the partitions of an `n`-element set; the Stirling
number of the second kind `S(n,k)` counts the partitions into exactly `k` blocks.
Grouping partitions by their number of blocks gives the classical identity

    Bₙ = Σ_{k=0}^{n} S(n, k).

Pinned Mathlib carries both `Nat.bell` (defined by the binomial recurrence
`B_{n+1} = Σ_i C(n,i)·B_{n-i}`) and `Nat.stirlingSecond` (defined by the triangular
recurrence `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)`), together with their basic
boundary values — but it does **not** connect them. This file fills that gap.

The bridge is a second, "horizontal" Stirling recurrence, also absent from Mathlib:

    S(n+1, k+1) = Σ_{j=0}^{n} C(n, j) · S(j, k),

(condition a partition of `{0,…,n}` into `k+1` blocks on the `j` elements lying
*outside* the block of the last point). Summing it over `k` turns the Stirling row
sum into the Bell binomial recurrence, so the two definitions agree.

## Main results (0 sorry, 0 axiom)
* `stirlingSecond_horizontal` — `S(n+1,k+1) = Σ_{j<n+1} C(n,j)·S(j,k)`.
* `bell_eq_sum_stirlingSecond` — `Bₙ = Σ_{k<n+1} S(n,k)`.

Fully machine-checked, no extra axioms, no `native_decide`.
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Tactic

namespace BellNumbersOQ01

open Finset

/-- **The horizontal recurrence for the Stirling numbers of the second kind.**
`S(n+1, k+1) = Σ_{j ≤ n} C(n,j)·S(j,k)`.  Absent from pinned Mathlib (which carries
only the triangular recurrence `stirlingSecond_succ_succ`). -/
theorem stirlingSecond_horizontal (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1)
      = ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k := by
  induction n generalizing k with
  | zero =>
    simp [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    -- LHS via the triangular recurrence:  S(n+2,k+1) = (k+1)·S(n+1,k+1) + S(n+1,k).
    rw [Nat.stirlingSecond_succ_succ]
    -- RHS: peel the `j = 0` term, then Pascal on the rest.
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ', Nat.choose_zero_right, one_mul, add_mul, Finset.sum_add_distrib]
    -- The shifted block `Σ_{i≤n} C(n,i+1)·S(i+1,k)` plus its missing `j=0` term is `g(n,k)`.
    have hshift : (∑ i ∈ range (n + 1), n.choose (i + 1) * Nat.stirlingSecond (i + 1) k)
          + Nat.stirlingSecond 0 k
        = ∑ j ∈ range (n + 1), n.choose j * Nat.stirlingSecond j k := by
      rw [Finset.sum_range_succ' (fun j => n.choose j * Nat.stirlingSecond j k) n,
        Finset.sum_range_succ (fun i => n.choose (i + 1) * Nat.stirlingSecond (i + 1) k) n]
      simp [Nat.choose_succ_self]
    -- Hence `Σ C(n,i+1)·S(i+1,k) + S(0,k) = S(n+1,k+1)` (the IH at `k`).
    have hS2 : (∑ i ∈ range (n + 1), n.choose (i + 1) * Nat.stirlingSecond (i + 1) k)
          + Nat.stirlingSecond 0 k = Nat.stirlingSecond (n + 1) (k + 1) := by
      rw [hshift, ih k]
    -- The unshifted block `Σ C(n,i)·S(i+1,k)` via the triangular recurrence + IH.
    cases k with
    | zero =>
      have hSum1zero :
          (∑ i ∈ range (n + 1), n.choose i * Nat.stirlingSecond (i + 1) 0) = 0 := by
        apply Finset.sum_eq_zero; intro x _; rw [Nat.stirlingSecond_succ_zero]; ring
      rw [hSum1zero, Nat.stirlingSecond_succ_zero]
      omega
    | succ k' =>
      have hSum1 : (∑ i ∈ range (n + 1), n.choose i * Nat.stirlingSecond (i + 1) (k' + 1))
          = (k' + 1) * Nat.stirlingSecond (n + 1) (k' + 1 + 1)
              + Nat.stirlingSecond (n + 1) (k' + 1) := by
        rw [ih (k' + 1), ih k', Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [Nat.stirlingSecond_succ_succ]
        ring
      rw [hSum1]
      omega

/-- **Bell numbers as the row sum of Stirling numbers of the second kind.**
`Bₙ = Σ_{k ≤ n} S(n,k)`.  Connects Mathlib's `Nat.bell` and `Nat.stirlingSecond`,
a bridge absent from pinned Mathlib. -/
theorem bell_eq_sum_stirlingSecond (n : ℕ) :
    Nat.bell n = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | (m + 1), ih =>
      -- For `j ≤ m`, the (padded) Stirling row sum is `bell j`: the tail terms vanish.
      have hInner : ∀ j ∈ range (m + 1),
          (∑ k ∈ range (m + 1), Nat.stirlingSecond j k) = Nat.bell j := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hsub : range (j + 1) ⊆ range (m + 1) := by
          intro x hx; rw [Finset.mem_range] at *; omega
        rw [← Finset.sum_subset hsub (fun k _ hk => Nat.stirlingSecond_eq_zero_of_lt
            (by rw [Finset.mem_range] at hk; omega))]
        exact (ih j hj).symm
      -- The Bell binomial recurrence rewritten as `Σ_j C(m,j)·bell j`.
      have hbell : Nat.bell (m + 1) = ∑ j ∈ range (m + 1), m.choose j * Nat.bell j := by
        rw [Nat.bell_succ, Fin.sum_univ_eq_sum_range (fun i => m.choose i * Nat.bell (m - i)) (m + 1),
          ← Finset.sum_range_reflect (fun j => m.choose j * Nat.bell j) (m + 1)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        simp only [Nat.add_sub_cancel]
        rw [Nat.choose_symm (by omega : i ≤ m)]
      rw [hbell, Finset.sum_range_succ' (fun k => Nat.stirlingSecond (m + 1) k) (m + 1),
        Nat.stirlingSecond_succ_zero, add_zero]
      simp_rw [stirlingSecond_horizontal]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => by rw [hInner j hj])

end BellNumbersOQ01
