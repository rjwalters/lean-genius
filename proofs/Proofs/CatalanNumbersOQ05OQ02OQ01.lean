import Mathlib
import Proofs.CatalanNumbersOQ05OQ02

/-!
# Row sums of Catalan's triangle: `Σₖ T(n,k) = catalan (n+1)`

`catalan-numbers-oq-05-oq-02-oq-01`

The parent entry (`catalan-numbers-oq-05-oq-02`, `Proofs/CatalanNumbersOQ05OQ02.lean`)
defines the ballot number / Catalan-triangle entry

  `ballotNumber n k = C(n+k, k) − C(n+k, n+1)`

and proves its closed form and the reflection-principle recurrence. This file
proves the **row-sum identity**: summing an entire row of the triangle reproduces
the *next* Catalan number,

  `Σ_{k=0}^{n} ballotNumber n k = catalan (n+1)`.

## A correction to the seeded statement

The seed problem stated the row sum as `C(2n+1, n)`. That is **false**: for `n = 1`
the row is `T(1,0) + T(1,1) = 1 + 1 = 2`, whereas `C(3,1) = 3`. The row sums are
in fact the Catalan numbers `1, 2, 5, 14, …` (`= catalan (n+1)`), exactly as the
problem's own plain-language paragraph and its "equivalently `catalan (n+1)`" note
say. We prove the correct identity.

## Proof outline

Write `A(n) = Σ_{k≤n} C(n+k, k)` and `B(n) = Σ_{k≤n} C(n+k, n+1)`. Since each
term satisfies `C(n+k, n+1) ≤ C(n+k, k)` (parent `ballotNumber_le`), the row sum is
`A(n) − B(n)` (proved in additive form to avoid truncated subtraction).

* `sum_choose_diag`  : `A(n) = C(2n+1, n+1)` — hockey stick (`Nat.sum_Icc_choose`).
* `sum_choose_reflected` : `B(n) = C(2n+1, n+2)` — hockey stick, dropping the zero `k=0` term.
* `choose_sub_eq_catalan` : `C(2n+1, n+1) = catalan (n+1) + C(2n+1, n+2)` — the
  arithmetic identity, via `succ_mul_catalan_eq_centralBinom`, Pascal + symmetry,
  and the absorption law `Nat.choose_succ_right_eq`.

Assembling these gives the main theorem `sum_ballotNumber_row`.

All results are `0`-sorry, `0`-axiom over `ℕ`.
-/

open Nat Finset

namespace CatalanNumbersOQ05OQ02OQ01

open CatalanNumbersOQ05OQ02 (ballotNumber ballotNumber_le)

/-- **Hockey stick, main diagonal.** `Σ_{k=0}^{n} C(n+k, k) = C(2n+1, n+1)`.

`C(n+k, k) = C(n+k, n)` by symmetry, and the reindexed sum over `Icc n (2n)` is a
direct instance of the hockey-stick identity `Nat.sum_Icc_choose`. -/
theorem sum_choose_diag (n : ℕ) :
    ∑ k ∈ range (n + 1), (n + k).choose k = (2 * n + 1).choose (n + 1) := by
  -- Replace `C(n+k, k)` by `C(n+k, n)` termwise.
  have hsymm : ∀ k ∈ range (n + 1), (n + k).choose k = (n + k).choose n := by
    intro k _
    rw [← Nat.choose_symm (show k ≤ n + k by omega)]
    congr 1
    omega
  rw [Finset.sum_congr rfl hsymm]
  -- Turn the target central binomial into the hockey-stick `Icc` sum, then reindex.
  rw [← Nat.sum_Icc_choose (2 * n) n, ← Nat.Ico_succ_right,
    Finset.sum_Ico_eq_sum_range]
  -- `∑ i ∈ range (2n+1-n), (n+i).choose n`, and `2n+1-n = n+1`.
  rw [show 2 * n + 1 - n = n + 1 by omega]

/-- **Hockey stick, reflected diagonal.** `Σ_{k=0}^{n} C(n+k, n+1) = C(2n+1, n+2)`.

The `k = 0` summand is `C(n, n+1) = 0`; the rest is again `Nat.sum_Icc_choose`. -/
theorem sum_choose_reflected (n : ℕ) :
    ∑ k ∈ range (n + 1), (n + k).choose (n + 1) = (2 * n + 1).choose (n + 2) := by
  rw [Finset.sum_range_succ']
  -- `(∑ i ∈ range n, (n+(i+1)).choose (n+1)) + (n+0).choose (n+1)`
  have h0 : (n + 0).choose (n + 1) = 0 := by
    simp [Nat.choose_eq_zero_of_lt]
  rw [h0, add_zero]
  -- Reindex the target `C(2n+1, n+2)` back to a `range` sum over `Icc (n+1) (2n)`.
  rw [← Nat.sum_Icc_choose (2 * n) (n + 1), ← Nat.Ico_succ_right,
    Finset.sum_Ico_eq_sum_range, show 2 * n + 1 - (n + 1) = n by omega]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

/-- **Arithmetic core.** `C(2n+1, n+1) = catalan (n+1) + C(2n+1, n+2)`.

Multiplying by `n+2`: `(n+2)·catalan (n+1) = centralBinom (n+1) = 2·C(2n+1, n+1)`
(Pascal + symmetry), while the absorption law gives `(n+2)·C(2n+1, n+2) = n·C(2n+1, n+1)`.
Hence `(n+2)·(catalan (n+1) + C(2n+1, n+2)) = (n+2)·C(2n+1, n+1)`, and we cancel `n+2`. -/
theorem choose_sub_eq_catalan (n : ℕ) :
    (2 * n + 1).choose (n + 1) = catalan (n + 1) + (2 * n + 1).choose (n + 2) := by
  -- `C(2n+1, n) = C(2n+1, n+1)` by symmetry.
  have hsym : (2 * n + 1).choose n = (2 * n + 1).choose (n + 1) := by
    rw [← Nat.choose_symm (show n + 1 ≤ 2 * n + 1 by omega)]
    congr 1
    omega
  -- `centralBinom (n+1) = 2 · C(2n+1, n+1)`.
  have h2 : (n + 1).centralBinom = 2 * (2 * n + 1).choose (n + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1) = (2 * n + 1) + 1 by ring,
      Nat.choose_succ_succ' (2 * n + 1) n, hsym]
    ring
  -- `(n+2) · catalan (n+1) = centralBinom (n+1)`.
  have h3 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  -- `(n+2) · catalan (n+1) = 2 · C(2n+1, n+1)`.
  have hA2 : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1).choose (n + 1) := h3.trans h2
  -- Absorption: `C(2n+1, n+2) · (n+2) = C(2n+1, n+1) · n`.
  have h1 : (2 * n + 1).choose (n + 2) * (n + 2) = (2 * n + 1).choose (n + 1) * n := by
    have h := Nat.choose_succ_right_eq (2 * n + 1) (n + 1)
    rw [show 2 * n + 1 - (n + 1) = n by omega] at h
    -- `h : C(2n+1, n+2) * (n+2) = C(2n+1, n+1) * n`   (note `(n+1)+1 = n+2`)
    simpa using h
  -- Multiply the goal through by `n+2` and cancel.
  have key : (n + 2) * (catalan (n + 1) + (2 * n + 1).choose (n + 2))
      = (n + 2) * (2 * n + 1).choose (n + 1) := by
    calc (n + 2) * (catalan (n + 1) + (2 * n + 1).choose (n + 2))
        = (n + 2) * catalan (n + 1) + (2 * n + 1).choose (n + 2) * (n + 2) := by ring
      _ = 2 * (2 * n + 1).choose (n + 1) + (2 * n + 1).choose (n + 1) * n := by rw [hA2, h1]
      _ = (n + 2) * (2 * n + 1).choose (n + 1) := by ring
  have := Nat.eq_of_mul_eq_mul_left (show 0 < n + 2 by omega) key
  omega

/-- **Additive split.** `(Σ ballotNumber n k) + (Σ C(n+k, n+1)) = Σ C(n+k, k)`.

Termwise, `ballotNumber n k + C(n+k, n+1) = C(n+k, k)` for `k ≤ n`, by
`Nat.sub_add_cancel` and the parent's well-posedness `ballotNumber_le`. -/
theorem sum_add_reflected (n : ℕ) :
    (∑ k ∈ range (n + 1), ballotNumber n k)
      + ∑ k ∈ range (n + 1), (n + k).choose (n + 1)
      = ∑ k ∈ range (n + 1), (n + k).choose k := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  show ((n + k).choose k - (n + k).choose (n + 1)) + (n + k).choose (n + 1) = (n + k).choose k
  exact Nat.sub_add_cancel (ballotNumber_le n k (by omega))

/-- **Row sums of Catalan's triangle are the Catalan numbers.**

`Σ_{k=0}^{n} ballotNumber n k = catalan (n+1)`. -/
theorem sum_ballotNumber_row (n : ℕ) :
    ∑ k ∈ range (n + 1), ballotNumber n k = catalan (n + 1) := by
  have hC := sum_add_reflected n
  rw [sum_choose_diag n, sum_choose_reflected n] at hC
  have hD := choose_sub_eq_catalan n
  omega

/-- Sanity checks: the first few row sums are `1, 2, 5, 14` (Catalan numbers). -/
example : ∑ k ∈ range 1, ballotNumber 0 k = 1 := by decide
example : ∑ k ∈ range 2, ballotNumber 1 k = 2 := by decide
example : ∑ k ∈ range 3, ballotNumber 2 k = 5 := by decide
example : ∑ k ∈ range 4, ballotNumber 3 k = 14 := by decide

end CatalanNumbersOQ05OQ02OQ01
