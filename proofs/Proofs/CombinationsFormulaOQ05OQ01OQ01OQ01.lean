import Mathlib

/-
# Two-Coefficient Closed Form for the Quadratically-Weighted Alternating Binomial Sum

## Open Question OQ-05-OQ-01-OQ-01-OQ-01

The parent (`CombinationsFormulaOQ05OQ01OQ01`) proves the *single*-coefficient
closed form for the **linearly** weighted partial alternating binomial sum,

  ∑_{k=0}^{j} (-1)^k · k · C(n, k) = n · (-1)^j · C(n-2, j-1)      (n ≥ 2),

obtained by one **absorption** step `k · C(n,k) = n · C(n-1, k-1)` followed by one
telescoping.  Its first open question asks whether the **quadratically** weighted
partial sum admits a closed form, obtained by absorbing `k² = k(k-1) + k` into two
row shifts.

This file answers that question.  The answer is a **two-coefficient** closed form
— a fixed `ℤ`-linear combination of two single binomials, one from row `n-3` and
one from row `n-2`:

  ∑_{k=0}^{j} (-1)^k · k² · C(n, k)
      = (-1)^j · ( n(n-1) · C(n-3, j-2) + n · C(n-2, j-1) )        (n ≥ 3).      (★)

So the quadratic weight needs exactly two coefficients where the linear weight
needed one: the `k(k-1)` part absorbs into the row *three below* (scaled by
`n(n-1)`), and the leftover `k` part absorbs into the row *two below* (scaled by
`n`), recovering the parent's term verbatim.

## Mechanism

The proof is a single induction on the cut-off, mirroring the parent.  The new
term `(i+3)² · C(m+3, i+3)` is reduced by **two** applications of the absorption
identity `(K+1)·C(N+1,K+1) = (N+1)·C(N,K)` (`Nat.add_one_mul_choose_eq`):

  (i+3)² · C(m+3, i+3)
    = (m+3)(m+2) · C(m+1, i+1) + (m+3) · C(m+2, i+2),

after which two Pascal steps `C(N+1,K+1) = C(N,K) + C(N,K+1)`
(`Nat.choose_succ_succ`) collapse the sum down to the two surviving coefficients.
The `(-1)` powers and the scalars are bookkept by `linear_combination`.

## Subtraction-free form

To avoid natural-number subtraction the identity is proved in the shifted form
(with `n = m+3`, `j = i+2`), valid for **all** `m, i`:

  ∑_{k=0}^{i+2} (-1)^k · k² · C(m+3, k)
      = (-1)^i · ( (m+3)(m+2) · C(m, i) + (m+3) · C(m+1, i+1) ).               (★')

## Results

1. `quad_weighted_partial_alternating_sum`      — (★') clean form, valid for all `m,i`.
2. `quad_weighted_partial_alternating_sum_sub`  — (★) literal `C(n-3,·)`/`C(n-2,·)`
   form, `n ≥ 3`.
3. `quad_weighted_partial_alternating_sum_stabilizes` — the quadratically weighted
   partial sums are `0` once `j ≥ n` (`n ≥ 3`).
4. `quad_weighted_full_row_eq_zero`             — the full quadratically weighted
   alternating row sum vanishes for `n ≥ 3`, the case `j = n` of (★).

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ05OQ01OQ01OQ01

open Finset

/-- **Main identity (subtraction-free form).** For all `m, i`,
    `∑_{k=0}^{i+2} (-1)^k · k² · C(m+3, k)
       = (-1)^i · ( (m+3)(m+2) · C(m, i) + (m+3) · C(m+1, i+1) )` in `ℤ`.

    Proof by induction on `i`.  The inductive step reduces the new weighted term
    `(i+3)² · C(m+3, i+3)` by two absorptions and then telescopes with two Pascal
    steps; `linear_combination` discharges the resulting polynomial identity. -/
theorem quad_weighted_partial_alternating_sum (m i : ℕ) :
    ∑ k ∈ range (i + 3), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * ((m + 3).choose k : ℤ))
      = (-1 : ℤ) ^ i *
          (((m : ℤ) + 3) * ((m : ℤ) + 2) * (m.choose i : ℤ)
            + ((m : ℤ) + 3) * ((m + 1).choose (i + 1) : ℤ)) := by
  induction i with
  | zero =>
    -- `range 3`: only `k = 1, 2` contribute.  Evaluate `C(m+3,2)` via one
    -- absorption (`C(m+3,1)`, `C(m,0)`, `C(m+1,1)` fall to `simp`), then
    -- `linear_combination`.
    have h2 : (2 : ℤ) * ((m + 3).choose 2 : ℤ) = ((m : ℤ) + 3) * ((m : ℤ) + 2) := by
      have hnat := Nat.add_one_mul_choose_eq (m + 2) 1
      rw [Nat.choose_one_right, show m + 2 + 1 = m + 3 by omega,
        show (1 : ℕ) + 1 = 2 by norm_num] at hnat
      have hc := congrArg (Nat.cast (R := ℤ)) hnat
      push_cast at hc
      linear_combination -hc
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast [Nat.choose_zero_right, Nat.choose_one_right]
    linear_combination (2 : ℤ) * h2
  | succ i ih =>
    rw [Finset.sum_range_succ, ih]
    -- Absorption `a`: `(i+3)·C(m+3,i+3) = (m+3)·C(m+2,i+2)`.
    have absorb_a : ((i : ℤ) + 3) * ((m + 3).choose (i + 3) : ℤ)
        = ((m : ℤ) + 3) * ((m + 2).choose (i + 2) : ℤ) := by
      have h := Nat.add_one_mul_choose_eq (m + 2) (i + 2)
      have h2 := congrArg (Nat.cast (R := ℤ)) h
      push_cast at h2
      linear_combination -h2
    -- Absorption `b`: `(i+2)·C(m+2,i+2) = (m+2)·C(m+1,i+1)`.
    have absorb_b : ((i : ℤ) + 2) * ((m + 2).choose (i + 2) : ℤ)
        = ((m : ℤ) + 2) * ((m + 1).choose (i + 1) : ℤ) := by
      have h := Nat.add_one_mul_choose_eq (m + 1) (i + 1)
      have h2 := congrArg (Nat.cast (R := ℤ)) h
      push_cast at h2
      linear_combination -h2
    -- Double absorption: `(i+3)²·C(m+3,i+3) = (m+3)(m+2)·C(m+1,i+1) + (m+3)·C(m+2,i+2)`.
    have absorbA : ((i : ℤ) + 3) ^ 2 * ((m + 3).choose (i + 3) : ℤ)
        = ((m : ℤ) + 3) * ((m : ℤ) + 2) * ((m + 1).choose (i + 1) : ℤ)
          + ((m : ℤ) + 3) * ((m + 2).choose (i + 2) : ℤ) := by
      linear_combination ((i : ℤ) + 3) * absorb_a + ((m : ℤ) + 3) * absorb_b
    -- Pascal `p1`: `C(m+1,i+1) = C(m,i) + C(m,i+1)`.
    have pascal1 : ((m + 1).choose (i + 1) : ℤ)
        = (m.choose i : ℤ) + (m.choose (i + 1) : ℤ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    -- Pascal `p2`: `C(m+2,i+2) = C(m+1,i+1) + C(m+1,i+2)`.
    have pascal2 : ((m + 2).choose (i + 2) : ℤ)
        = ((m + 1).choose (i + 1) : ℤ) + ((m + 1).choose (i + 2) : ℤ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    push_cast
    linear_combination (-((-1 : ℤ) ^ i)) * absorbA
      + (-((-1 : ℤ) ^ i) * (((m : ℤ) + 3) * ((m : ℤ) + 2))) * pascal1
      + (-((-1 : ℤ) ^ i) * ((m : ℤ) + 3)) * pascal2

/-- **Quadratically weighted partial sum (literal form).** For `n ≥ 3` and any `j`,
    `∑_{k=0}^{j+2} (-1)^k · k² · C(n, k)
       = (-1)^j · ( n(n-1)·C(n-3, j) + n·C(n-2, j+1) )` in `ℤ`.

    This is `(★)` with the cut-off written as `j+2` (so that `j-2 = j` and
    `j-1 = j+1` after the shift), exhibiting the two coefficients as binomials of
    rows `n-3` and `n-2`. -/
theorem quad_weighted_partial_alternating_sum_sub {n : ℕ} (hn : 3 ≤ n) (j : ℕ) :
    ∑ k ∈ range (j + 3), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (n.choose k : ℤ))
      = (-1 : ℤ) ^ j *
          ((n : ℤ) * ((n : ℤ) - 1) * ((n - 3).choose j : ℤ)
            + (n : ℤ) * ((n - 2).choose (j + 1) : ℤ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : (m + 3 - 3) = m := by omega
  have e2 : (m + 3 - 2) = m + 1 := by omega
  rw [quad_weighted_partial_alternating_sum m j, e1, e2]
  push_cast
  ring

/-- **Stabilisation.** Once the cut-off reaches the row length the quadratically
    weighted partial sums are already `0`: for `n ≥ 3` and `j ≥ n`,
    `∑_{k=0}^{j} (-1)^k · k² · C(n, k) = 0`.

    Reason: the closed form is `(-1)^j(n(n-1)·C(n-3,j-2) + n·C(n-2,j-1))`, and both
    binomials vanish because `j - 2 ≥ n - 2 > n - 3` and `j - 1 ≥ n - 1 > n - 2`. -/
theorem quad_weighted_partial_alternating_sum_stabilizes {n : ℕ} (hn : 3 ≤ n) {j : ℕ}
    (hj : n ≤ j) :
    ∑ k ∈ range (j + 1), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (n.choose k : ℤ)) = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rw [quad_weighted_partial_alternating_sum_sub hn i]
  have h1 : (n - 3).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h2 : (n - 2).choose (i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h1, h2]; simp

/-- **Full quadratically weighted alternating row sum vanishes** for `n ≥ 3`,
    obtained as the special case `j = n` of the partial closed form. -/
theorem quad_weighted_full_row_eq_zero {n : ℕ} (hn : 3 ≤ n) :
    ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (n.choose k : ℤ)) = 0 :=
  quad_weighted_partial_alternating_sum_stabilizes hn (le_refl n)

/-- Sanity check, row `n = 4`, cut-off `j = 2`:
    `0 - 1·C(4,1) + 4·C(4,2) = -4 + 24 = 20`, and the closed form gives
    `(+1)·(4·3·C(1,0) + 4·C(2,1)) = 12 + 8 = 20`. -/
example :
    ∑ k ∈ range 3, ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (Nat.choose 4 k : ℤ)) = 20 := by decide

/-- Sanity check of the closed form at `n = 4, j = 3`:
    LHS `= 0 - 4 + 24 - 9·C(4,3) = 20 - 36 = -16`;
    RHS `= (-1)^3·(4·3·C(1,1) + 4·C(2,2)) = -(12 + 4) = -16`. -/
example :
    ∑ k ∈ range 4, ((-1 : ℤ) ^ k * (k : ℤ) ^ 2 * (Nat.choose 4 k : ℤ)) = -16 := by decide

end CombinationsFormulaOQ05OQ01OQ01OQ01
