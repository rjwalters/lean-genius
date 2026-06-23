import Mathlib

/-
# A Two-Coefficient Closed Form for the Quadratically-Weighted Partial Alternating Binomial Sum

## Open Question OQ-05-OQ-01-OQ-01-OQ-01

The parent (`CombinationsFormulaOQ05OQ01OQ01`) gives the sharp single-coefficient
closed form for the **linearly weighted partial** alternating binomial sum,

  ∑_{k=0}^{j} (-1)^k · k · C(n, k) = n · (-1)^j · C(n-2, j-1)      (n ≥ 2),

and asks (its first open question): does the **quadratically weighted** partial
sum admit an analogous closed form, obtained by absorbing `k² = k(k-1) + k` into
two row shifts?

This file answers that question.  The quadratic weight does **not** collapse to a
single binomial — instead it produces a *two-coefficient* closed form, one
binomial from each of the two row shifts:

  ∑_{k=0}^{j} (-1)^k · k² · C(n, k)
      = (-1)^j · n · ( (n-1) · C(n-3, j-2) + C(n-2, j-1) )      (n ≥ 3).      (★)

The mechanism is the identity `k² = k(k-1) + k`.  The piece `k(k-1)·C(n,k) =
n(n-1)·C(n-2,k-2)` shifts the row down by two, contributing the binomial
`C(n-3, j-2)` (scaled by `n(n-1)`); the piece `k·C(n,k) = n·C(n-1,k-1)` shifts
the row down by one, contributing `C(n-2, j-1)` (scaled by `n`), exactly the
parent's single coefficient.  So one quadratic weight produces precisely **two**
surviving binomials — the predicted two-coefficient form.

Specialising `j` to the full row recovers the classical vanishing of the
quadratically weighted alternating row sum `∑_{k=0}^{n} (-1)^k k² C(n,k) = 0`
for `n ≥ 3` (a second finite difference of a constant sequence killing a degree
`< n` polynomial weight).

Equivalently, with no natural-number subtraction (the form actually proved by
induction below),

  ∑_{k=0}^{j+2} (-1)^k · k² · C(n+3, k)
      = (-1)^j · (n+3) · ( (n+2) · C(n, j) + C(n+1, j+1) )     (all n, j).    (★')

## Results

1. `quad_weighted_partial_alternating_sum`            — (★') clean form, all `n, j`.
2. `quad_weighted_partial_alternating_sum_sub`        — (★) literal `C(n-3,·)`,`C(n-2,·)` form, `n ≥ 3`.
3. `quad_weighted_partial_alternating_sum_stabilizes` — the partial sums are `0` once `j ≥ n` (`n ≥ 3`).
4. `quad_weighted_full_row_eq_zero`                   — recovers the anchor `∑_{k=0}^{n} (-1)^k k² C(n,k) = 0` (`n ≥ 3`).

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ05OQ01OQ01OQ01

open Finset

/-- **Main identity (subtraction-free form).** For all `n, j`,
    `∑_{k=0}^{j+2} (-1)^k · k² · C(n+3, k) = (n+3) · (-1)^j · ((n+2)·C(n,j) + C(n+1,j+1))`
    in `ℤ`.

    Proof by induction on `j`.  The inductive step rewrites the new weighted term
    `(j+3)² · C(n+3, j+3)` via two applications of the binomial **absorption
    identity** `(k+1)·C(m+1,k+1) = (m+1)·C(m,k)` (`Nat.add_one_mul_choose_eq`) into
    `(n+3)·((n+2)·C(n+1,j+1) + C(n+2,j+2))` (lemma `key`), and then two uses of
    Pascal's rule `C(m+1,k+1) = C(m,k) + C(m,k+1)` (`Nat.choose_succ_succ`)
    telescope the two surviving coefficients down to row `n`.  All `(-1)`-power
    bookkeeping and the scalars are discharged by `linear_combination` over `ring`. -/
theorem quad_weighted_partial_alternating_sum (n j : ℕ) :
    ∑ k ∈ range (j + 3), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * ((n + 3).choose k : ℤ))
      = (-1 : ℤ) ^ j * (n + 3 : ℤ)
          * (((n : ℤ) + 2) * (n.choose j : ℤ) + ((n + 1).choose (j + 1) : ℤ)) := by
  induction j with
  | zero =>
    -- `∑_{k=0}^{2} = 0 - C(n+3,1) + 4·C(n+3,2)`; uses `2·C(n+3,2) = (n+3)(n+2)`.
    have h := Nat.add_one_mul_choose_eq (n + 2) 1
    have h2 := congrArg (Nat.cast (R := ℤ)) h
    push_cast [Nat.choose_one_right] at h2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.choose_one_right, Nat.choose_zero_right]
    push_cast
    linear_combination -2 * h2
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    -- Absorption I: `(n+3)·C(n+2,j+2) = C(n+3,j+3)·(j+3)`.
    have hI : ((n : ℤ) + 3) * ((n + 2).choose (j + 2) : ℤ)
        = ((n + 3).choose (j + 3) : ℤ) * ((j : ℤ) + 3) := by
      have h := Nat.add_one_mul_choose_eq (n + 2) (j + 2)
      have h2 := congrArg (Nat.cast (R := ℤ)) h
      push_cast at h2
      linear_combination h2
    -- Absorption II: `(n+2)·C(n+1,j+1) = C(n+2,j+2)·(j+2)`.
    have hII : ((n : ℤ) + 2) * ((n + 1).choose (j + 1) : ℤ)
        = ((n + 2).choose (j + 2) : ℤ) * ((j : ℤ) + 2) := by
      have h := Nat.add_one_mul_choose_eq (n + 1) (j + 1)
      have h2 := congrArg (Nat.cast (R := ℤ)) h
      push_cast at h2
      linear_combination h2
    -- The new weighted term, rewritten by the two absorptions.
    have key : ((j : ℤ) + 3) ^ 2 * ((n + 3).choose (j + 3) : ℤ)
        = ((n : ℤ) + 3)
            * (((n : ℤ) + 2) * ((n + 1).choose (j + 1) : ℤ)
                + ((n + 2).choose (j + 2) : ℤ)) := by
      linear_combination (-(j : ℤ) - 3) * hI + (-(n : ℤ) - 3) * hII
    -- Pascal a: `C(n+1,j+1) = C(n,j) + C(n,j+1)`.
    have pa : ((n + 1).choose (j + 1) : ℤ) = (n.choose j : ℤ) + (n.choose (j + 1) : ℤ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    -- Pascal b: `C(n+2,j+2) = C(n+1,j+1) + C(n+1,j+2)`.
    have pb : ((n + 2).choose (j + 2) : ℤ)
        = ((n + 1).choose (j + 1) : ℤ) + ((n + 1).choose (j + 2) : ℤ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    push_cast
    linear_combination (-((-1 : ℤ) ^ j)) * key
      + (-((-1 : ℤ) ^ j) * ((n : ℤ) + 3) * ((n : ℤ) + 2)) * pa
      + (-((-1 : ℤ) ^ j) * ((n : ℤ) + 3)) * pb

/-- **Two-coefficient closed form (literal subtraction form).** For `n ≥ 3` and any
    `j`,
    `∑_{k=0}^{j+2} (-1)^k · k² · C(n,k) = (-1)^j · n · ((n-1)·C(n-3,j) + C(n-2,j+1))`
    in `ℤ`.

    This is `(★)` with the cut-off written as `j+2`, exhibiting the two surviving
    coefficients as binomials of rows `n-3` and `n-2`. -/
theorem quad_weighted_partial_alternating_sum_sub {n : ℕ} (hn : 3 ≤ n) (j : ℕ) :
    ∑ k ∈ range (j + 3), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (n.choose k : ℤ))
      = (-1 : ℤ) ^ j * (n : ℤ)
          * (((n : ℤ) - 1) * ((n - 3).choose j : ℤ) + ((n - 2).choose (j + 1) : ℤ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 3 = m from rfl, show m + 3 - 2 = m + 1 from rfl,
    quad_weighted_partial_alternating_sum m j]
  push_cast; ring

/-- **Stabilisation.** Once the cut-off reaches the row length the quadratically
    weighted partial sums are already `0`: for `n ≥ 3` and `j ≥ n`,
    `∑_{k=0}^{j} (-1)^k · k² · C(n, k) = 0`.

    Reason: both binomials in the closed form vanish, `C(n-3, j-2) = 0` and
    `C(n-2, j-1) = 0`, since `j - 2 ≥ n - 2 > n - 3`. -/
theorem quad_weighted_partial_alternating_sum_stabilizes {n : ℕ} (hn : 3 ≤ n) {j : ℕ}
    (hj : n ≤ j) :
    ∑ k ∈ range (j + 1), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (n.choose k : ℤ)) = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rw [show i + 2 + 1 = i + 3 from rfl, quad_weighted_partial_alternating_sum_sub hn i]
  have h1 : (n - 3).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h2 : (n - 2).choose (i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h1, h2]; simp

/-- **Recovers the classical anchor.** The full quadratically weighted alternating
    row sum vanishes for `n ≥ 3`, obtained as the special case `j = n` of the
    closed form (both binomials are `0`). -/
theorem quad_weighted_full_row_eq_zero {n : ℕ} (hn : 3 ≤ n) :
    ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (n.choose k : ℤ)) = 0 :=
  quad_weighted_partial_alternating_sum_stabilizes hn (le_refl n)

/-- Sanity check of the clean closed form at `n = 0, j = 0`:
    LHS `= 0 - 1·C(3,1) + 4·C(3,2) = -3 + 12 = 9`; RHS `= 3·((2)·C(0,0) + C(1,1)) = 9`. -/
example :
    ∑ k ∈ range 3, ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (Nat.choose 3 k : ℤ)) = 9 := by decide

/-- Sanity check of the full-row vanishing at `n = 4`:
    `0 - 1·4 + 4·6 - 9·4 + 16·1 = -4 + 24 - 36 + 16 = 0`. -/
example :
    ∑ k ∈ range 5, ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (Nat.choose 4 k : ℤ)) = 0 := by decide

end CombinationsFormulaOQ05OQ01OQ01OQ01
