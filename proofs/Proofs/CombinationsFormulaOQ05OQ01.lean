import Mathlib

/-
# Telescoping Partial Sums of an Alternating Binomial Row

## Open Question OQ-05-OQ-01

The parent (`CombinationsFormulaOQ05`) records the *full* alternating row sum of
Pascal's triangle, `∑_{k=0}^{n} (-1)^k C(n,k) = 0` for `n ≥ 1`
(`Int.alternating_sum_range_choose_of_ne`).  That identity says the complete
alternating row cancels, but it is silent about the **partial** sums
`∑_{k=0}^{j} (-1)^k C(n,k)` for `j < n`.

This file proves the sharp closed form for every partial sum:

  ∑_{k=0}^{j} (-1)^k · C(n, k) = (-1)^j · C(n-1, j)            (n ≥ 1).             (★)

Equivalently, with no natural-number subtraction,

  ∑_{k=0}^{j} (-1)^k · C(n+1, k) = (-1)^j · C(n, j)            (all n).             (★')

Mathlib has only the full-row vanishing (`Int.alternating_sum_range_choose`,
`Int.alternating_sum_range_choose_of_ne`).  The partial closed form (★) is not in
Mathlib; it is a genuine refinement — the full-row identity falls out of (★) by
taking `j = n` and using `C(n-1, n) = 0`.

## Why a closed form at all?

Write `aₖ := (-1)^k C(n,k)`.  Pascal's rule `C(n,j+1) = C(n-1,j) + C(n-1,j+1)`
makes the running sum **telescope**: the `j`-th partial sum is, up to sign, a
single binomial coefficient of the *previous* row.  Concretely, the sequence of
partial sums is exactly the alternating row of `C(n-1, ·)` read off term by term.
This is the discrete analogue of the fact that `(1-x)^n` has antiderivative-like
partial sums governed by `(1-x)^{n-1}`; it is the binomial-coefficient form of
the finite-difference operator `Δ⁻¹`.

## Results

1. `partial_alternating_sum`        — (★') clean form, valid for all `n`.
2. `partial_alternating_sum_pred`   — (★) literal `C(n-1,j)` form, `n ≥ 1`.
3. `partial_alternating_sum_stabilizes` — partial sums are `0` once `j ≥ n` (`n ≥ 1`).
4. `full_alternating_row_eq_zero`   — recovers the parent anchor from (★') alone.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ05OQ01

open Finset

/-- **Main identity (subtraction-free form).** For all `n, j`,
    `∑_{k=0}^{j} (-1)^k C(n+1, k) = (-1)^j C(n, j)` in `ℤ`.

    Proof by induction on `j`; the inductive step is precisely Pascal's rule
    `C(n+1, j+1) = C(n, j) + C(n, j+1)`, which is what makes the partial sums
    telescope down to a single binomial coefficient of row `n`. -/
theorem partial_alternating_sum (n j : ℕ) :
    ∑ k ∈ range (j + 1), ((-1 : ℤ) ^ k * ((n + 1).choose k : ℤ))
      = (-1 : ℤ) ^ j * (n.choose j : ℤ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    -- Pascal's rule, cast to ℤ.
    have pascal : ((n + 1).choose (j + 1) : ℤ)
        = (n.choose j : ℤ) + (n.choose (j + 1) : ℤ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    rw [pascal, pow_succ]
    ring

/-- **Telescoping partial sum (literal form).** For `n ≥ 1` and any `j`,
    `∑_{k=0}^{j} (-1)^k C(n, k) = (-1)^j C(n-1, j)` in `ℤ`. -/
theorem partial_alternating_sum_pred {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    ∑ k ∈ range (j + 1), ((-1 : ℤ) ^ k * (n.choose k : ℤ))
      = (-1 : ℤ) ^ j * ((n - 1).choose j : ℤ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa using partial_alternating_sum m j

/-- **Stabilisation.** Once the cut-off reaches the row length the partial sums
    are already `0`: for `n ≥ 1` and `j ≥ n`,
    `∑_{k=0}^{j} (-1)^k C(n, k) = 0`.  (The tail terms `C(n, k)` with `k > n` are
    zero, so all partial sums past the row coincide with the full row sum.) -/
theorem partial_alternating_sum_stabilizes {n : ℕ} (hn : n ≠ 0) {j : ℕ}
    (hj : n ≤ j) :
    ∑ k ∈ range (j + 1), ((-1 : ℤ) ^ k * (n.choose k : ℤ)) = 0 := by
  rw [partial_alternating_sum_pred hn j]
  -- `C(n-1, j) = 0` because `j ≥ n > n - 1`.
  have : (n - 1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [this]; simp

/-- **Recovers the parent anchor.** The full alternating row sum vanishes for
    `n ≥ 1`.  This is `Int.alternating_sum_range_choose_of_ne`, here obtained as
    the special case `j = n` of the partial closed form (with `C(n-1, n) = 0`). -/
theorem full_alternating_row_eq_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ k * (n.choose k : ℤ)) = 0 :=
  partial_alternating_sum_stabilizes hn (le_refl n)

/-- Sanity check, row `n = 4`, cut-off `j = 2`:
    `C(4,0) - C(4,1) + C(4,2) = 1 - 4 + 6 = 3 = (+1)·C(3,2) = 3`. -/
example :
    ∑ k ∈ range 3, ((-1 : ℤ) ^ k * (Nat.choose 4 k : ℤ)) = 3 := by decide

/-- Sanity check of the closed form at `n = 5, j = 3`:
    LHS `= 1 - 5 + 10 - 10 = -4`; RHS `= (-1)^3 · C(4,3) = -4`. -/
example :
    ∑ k ∈ range 4, ((-1 : ℤ) ^ k * (Nat.choose 5 k : ℤ))
      = (-1 : ℤ) ^ 3 * (Nat.choose 4 3 : ℤ) := by decide

end CombinationsFormulaOQ05OQ01
