import Mathlib

/-
# The Hockey-Stick Identity and the Figurate-Number Tower

## Open Question OQ-06

Fix a column index `k` in Pascal's triangle and walk down the diagonal
`C(k,k), C(k+1,k), C(k+2,k), …`.  The **hockey-stick** (a.k.a. *Christmas-stocking*)
identity states that the partial sums along this diagonal land one row below and one
column to the right:

  ∑_{m=k}^{n} C(m, k) = C(n+1, k+1).

In Pascal's triangle the summands trace the long shaft of a hockey stick and the
answer is the blade.  Mathlib packages the identity as `Nat.sum_Icc_choose`, summed
over the closed interval `Icc k n`.

## Contribution

The sibling file `CombinationsFormulaOQ01` records the *shifted* presentation
`∑_{i<n+1} C(i + r, r) = C(n + r + 1, r + 1)` proved by a hand induction.  This file
takes the **column-indexed** viewpoint instead and pushes it through to its classical
consequences, the *figurate numbers*:

1. `hockey_stick_Icc`   — the identity in Mathlib's interval form `∑_{m ∈ Icc k n}`.
2. `hockey_stick_range` — the reformulation over `Finset.range (n+1)`, valid because
   the low terms `C(m, k)` with `m < k` vanish (`Nat.choose_eq_zero_of_lt`).
3. `triangular_eq_choose` — the `k = 1` slice: `0 + 1 + ⋯ + n = C(n+1, 2)`, the `n`-th
   **triangular number** as a binomial coefficient, plus the closed form `n(n+1)/2`.
4. `tetrahedral_eq_choose` — the `k = 2` slice: `∑_{m≤n} C(m, 2) = C(n+1, 3)`, the
   **tetrahedral numbers**.
5. `sum_triangular_eq_tetrahedral` — assembling the tower: the sum of the first `n+1`
   triangular numbers `T_m = C(m+1, 2)` is the tetrahedral number `C(n+2, 3)`.

The column index `k` is exactly the "dimension" of the figurate number: `k = 1` counts
points on a line, `k = 2` triangles, `k = 3` tetrahedra, and the hockey-stick identity
is the single statement that each layer is the running total of the one beneath it.

## Mathematical Context

`Nat.sum_Icc_choose` is itself a telescoping consequence of Pascal's rule
`C(m+1, k+1) = C(m, k) + C(m, k+1)`.  Reading it as a recurrence on the partial sums
gives the figurate-number recurrences `T_{n} = T_{n-1} + n` and `Te_n = Te_{n-1} + T_n`,
which is why the same identity specialises to every column at once.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ06

open Finset

/-- **Hockey-stick identity (interval form).**  Summing column `k` of Pascal's triangle
    from row `k` to row `n` gives the single entry `C(n+1, k+1)`.  This is exactly
    `Nat.sum_Icc_choose`, restated as the anchor for the developments below. -/
theorem hockey_stick_Icc (n k : ℕ) :
    ∑ m ∈ Finset.Icc k n, Nat.choose m k = Nat.choose (n + 1) (k + 1) :=
  Nat.sum_Icc_choose n k

/-- **Hockey-stick identity (range form).**  The same sum taken over the full initial
    segment `Finset.range (n+1) = {0, 1, …, n}`.  Extending the index range down to `0`
    changes nothing because `C(m, k) = 0` whenever `m < k`. -/
theorem hockey_stick_range (n k : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose m k = Nat.choose (n + 1) (k + 1) := by
  rw [← hockey_stick_Icc n k]
  refine (Finset.sum_subset ?_ ?_).symm
  · -- `Icc k n ⊆ range (n+1)`
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  · -- the extra indices `m < k` contribute `0`
    intro m hm hmIcc
    rw [Finset.mem_range] at hm
    rw [Finset.mem_Icc] at hmIcc
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- **Triangular numbers as binomial coefficients.**  The `k = 1` slice of the
    hockey-stick identity: `0 + 1 + ⋯ + n = C(n+1, 2)`. -/
theorem triangular_eq_choose (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), m = Nat.choose (n + 1) 2 := by
  rw [← hockey_stick_range n 1]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Nat.choose_one_right]

/-- The triangular number `C(n+1, 2)` in its familiar closed form `n(n+1)/2`. -/
theorem triangular_closed_form (n : ℕ) :
    Nat.choose (n + 1) 2 = n * (n + 1) / 2 := by
  rw [Nat.choose_two_right]
  congr 1
  simp only [Nat.add_sub_cancel]
  ring

/-- **Tetrahedral numbers as binomial coefficients.**  The `k = 2` slice of the
    hockey-stick identity: `∑_{m ≤ n} C(m, 2) = C(n+1, 3)`. -/
theorem tetrahedral_eq_choose (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose m 2 = Nat.choose (n + 1) 3 :=
  hockey_stick_range n 2

/-- **The figurate tower.**  The sum of the first `n+1` triangular numbers
    `T_m = C(m+1, 2)` is the tetrahedral number `C(n+2, 3)`.  This is the hockey-stick
    identity for column `2` after dropping the vanishing `C(0, 2) = 0` term. -/
theorem sum_triangular_eq_tetrahedral (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose (m + 1) 2 = Nat.choose (n + 2) 3 := by
  have h := hockey_stick_range (n + 1) 2
  rw [Finset.sum_range_succ'] at h
  simpa using h

-- Concrete verifications.
/-- `1 + 2 + 3 + 4 = 10 = C(5, 2)`. -/
example : ∑ m ∈ Finset.range 5, m = Nat.choose 5 2 := by decide
/-- `C(2,2) + C(3,2) + C(4,2) = 1 + 3 + 6 = 10 = C(5, 3)`. -/
example : ∑ m ∈ Finset.range 5, Nat.choose m 2 = Nat.choose 5 3 := by decide
/-- The triangular numbers `T_0 + ⋯ + T_4 = 0 + 1 + 3 + 6 + 10 = 20 = C(6, 3)`. -/
example : ∑ m ∈ Finset.range 5, Nat.choose (m + 1) 2 = Nat.choose 6 3 := by decide

end CombinationsFormulaOQ06
