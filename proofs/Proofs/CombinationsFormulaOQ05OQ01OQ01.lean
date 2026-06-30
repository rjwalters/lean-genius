import Mathlib

/-
# Closed Form for the Weighted Partial Alternating Binomial Sum

## Open Question OQ-05-OQ-01-OQ-01

The grandparent (`CombinationsFormulaOQ05`) records the vanishing of the *full*
**weighted** alternating row sum, `∑_{k=0}^{n} (-1)^k · k · C(n,k) = 0` for
`n ≥ 2`.  The parent (`CombinationsFormulaOQ05OQ01`) gives the closed form for
the *unweighted* **partial** sums, `∑_{k=0}^{j} (-1)^k C(n,k) = (-1)^j C(n-1,j)`.

This file answers the parent's open question by combining both refinements:
it gives the sharp single-coefficient closed form for the **weighted partial**
sum, valid for every cut-off `j`:

  ∑_{k=0}^{j} (-1)^k · k · C(n, k) = n · (-1)^j · C(n-2, j-1)      (n ≥ 2).      (★)

So, just like the unweighted partial sum is a single binomial of the *previous*
row, the weighted partial sum is a single binomial of the row *two below*,
scaled by `n` — and it stabilises to `0` exactly when `j ≥ n`, recovering the
grandparent's full-row vanishing as the special case `j = n`.

## Why a closed form at all?

Two mechanisms combine.  First, the **absorption identity**
`k · C(n,k) = n · C(n-1, k-1)` turns the weight `k` into a shift of the row,
converting the weighted sum on row `n` into `n` times an *unweighted* partial
sum on row `n-1`.  Second, that unweighted partial sum telescopes to a single
binomial of row `n-2` (the parent's mechanism).  The net effect is one
absorption followed by one telescoping, producing the single coefficient
`n · (-1)^j · C(n-2, j-1)`.

Equivalently, with no natural-number subtraction (the form actually proved by
induction below),

  ∑_{k=0}^{j+1} (-1)^k · k · C(n+2, k) = (n+2) · (-1)^{j+1} · C(n, j)   (all n,j).  (★')

## Results

1. `weighted_partial_alternating_sum`       — (★') clean form, valid for all `n,j`.
2. `weighted_partial_alternating_sum_sub`    — (★) literal `C(n-2,j-1)` form, `n ≥ 2`.
3. `weighted_partial_alternating_sum_stabilizes` — the weighted partial sums are
   `0` once `j ≥ n` (`n ≥ 2`).
4. `weighted_full_row_eq_zero`               — recovers the grandparent anchor
   `∑_{k=0}^{n} (-1)^k k C(n,k) = 0` (`n ≥ 2`) from (★') alone.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ05OQ01OQ01

open Finset

/-- **Main identity (subtraction-free form).** For all `n, j`,
    `∑_{k=0}^{j+1} (-1)^k · k · C(n+2, k) = (n+2) · (-1)^{j+1} · C(n, j)` in `ℤ`.

    Proof by induction on `j`.  The inductive step uses the binomial **absorption
    identity** `(k+1)·C(n+1,k+1) = (n+1)·C(n,k)` (`Nat.succ_mul_choose_eq`) to
    rewrite the new weighted term as a binomial of row `n+1`, followed by Pascal's
    rule `C(n+1,j+1) = C(n,j) + C(n,j+1)` to telescope down to a single binomial of
    row `n`. -/
theorem weighted_partial_alternating_sum (n j : ℕ) :
    ∑ k ∈ range (j + 2), ((-1 : ℤ) ^ k * (k : ℤ) * ((n + 2).choose k : ℤ))
      = (n + 2 : ℤ) * (-1 : ℤ) ^ (j + 1) * (n.choose j : ℤ) := by
  induction j with
  | zero =>
    -- `∑_{k=0}^{1} = 0 - C(n+2,1) = -(n+2)`, and `(n+2)·(-1)·C(n,0) = -(n+2)`.
    simp [Finset.sum_range_succ, Nat.choose_one_right]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    -- Absorption: `(j+2)·C(n+2,j+2) = (n+2)·C(n+1,j+1)` (cast of `Nat.add_one_mul_choose_eq`).
    have absorb : ((j : ℤ) + 2) * ((n + 2).choose (j + 2) : ℤ)
        = ((n : ℤ) + 2) * ((n + 1).choose (j + 1) : ℤ) := by
      -- `h : (n+2) * (n+1).choose (j+1) = (n+2).choose (j+2) * (j+2)`
      have h := Nat.add_one_mul_choose_eq (n + 1) (j + 1)
      have h2 := congrArg (Nat.cast (R := ℤ)) h
      push_cast at h2
      linear_combination -h2
    -- Pascal: `C(n+1,j+1) = C(n,j) + C(n,j+1)`.
    have pascal : ((n + 1).choose (j + 1) : ℤ)
        = (n.choose j : ℤ) + (n.choose (j + 1) : ℤ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    -- Combine via one absorption and one Pascal step; the `(-1)` powers and the
    -- scalar `n+2` are bookkept by `ring` inside `linear_combination`.
    push_cast
    linear_combination (-((-1 : ℤ) ^ (j + 1))) * absorb
      + (-((-1 : ℤ) ^ (j + 1)) * ((n : ℤ) + 2)) * pascal

/-- **Telescoping weighted partial sum (literal form).** For `n ≥ 2` and any `j`,
    `∑_{k=0}^{j+1} (-1)^k · k · C(n, k) = n · (-1)^{j+1} · C(n-2, j)` in `ℤ`.

    This is `(★)` with the cut-off written as `j+1` (so that `j-1 = j` after the
    shift), exhibiting the single coefficient as a binomial of row `n-2`. -/
theorem weighted_partial_alternating_sum_sub {n : ℕ} (hn : 2 ≤ n) (j : ℕ) :
    ∑ k ∈ range (j + 2), ((-1 : ℤ) ^ k * (k : ℤ) * (n.choose k : ℤ))
      = (n : ℤ) * (-1 : ℤ) ^ (j + 1) * ((n - 2).choose j : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using weighted_partial_alternating_sum m j

/-- **Stabilisation.** Once the cut-off reaches the row length the weighted partial
    sums are already `0`: for `n ≥ 2` and `j ≥ n`,
    `∑_{k=0}^{j} (-1)^k · k · C(n, k) = 0`.

    Reason: the closed form is `n·(-1)^j·C(n-2, j-1)`, and `C(n-2, j-1) = 0` because
    `j - 1 ≥ n - 1 > n - 2`. -/
theorem weighted_partial_alternating_sum_stabilizes {n : ℕ} (hn : 2 ≤ n) {j : ℕ}
    (hj : n ≤ j) :
    ∑ k ∈ range (j + 1), ((-1 : ℤ) ^ k * (k : ℤ) * (n.choose k : ℤ)) = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [weighted_partial_alternating_sum_sub hn i]
  -- `C(n-2, i) = 0` since `i ≥ n - 1 > n - 2`.
  have : (n - 2).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [this]; simp

/-- **Recovers the grandparent anchor.** The full weighted alternating row sum
    vanishes for `n ≥ 2`.  This is the content of `CombinationsFormulaOQ05`, here
    obtained as the special case `j = n` of the weighted partial closed form
    (with `C(n-2, n-1) = 0`). -/
theorem weighted_full_row_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ k * (k : ℤ) * (n.choose k : ℤ)) = 0 :=
  weighted_partial_alternating_sum_stabilizes hn (le_refl n)

/-- Sanity check, row `n = 4`, cut-off `j = 2`:
    `0 - 1·C(4,1) + 2·C(4,2) = -4 + 12 = 8 = 4·(+1)·C(2,1) = 8`. -/
example :
    ∑ k ∈ range 3, ((-1 : ℤ) ^ k * (k : ℤ) * (Nat.choose 4 k : ℤ)) = 8 := by decide

/-- Sanity check of the closed form at `n = 5, j = 3`:
    LHS `= 0 - 5 + 2·10 - 3·10 = -15`; RHS `= 5·(-1)^3·C(3,2) = -15`. -/
example :
    ∑ k ∈ range 4, ((-1 : ℤ) ^ k * (k : ℤ) * (Nat.choose 5 k : ℤ))
      = (5 : ℤ) * (-1 : ℤ) ^ 3 * (Nat.choose 3 2 : ℤ) := by decide

end CombinationsFormulaOQ05OQ01OQ01
