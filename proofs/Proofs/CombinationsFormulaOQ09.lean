import Mathlib

/-
# Weighted Binomial Sums: the First and Second Moments of a Row of Pascal's Triangle

## Open Question OQ-09

The row-sum identity `∑_{k=0}^{n} C(n,k) = 2ⁿ` and the alternating-sum identity
`∑_{k=0}^{n} (-1)ᵏ C(n,k) = 0` are already in the gallery.  This file proves the
two *weighted* companions — the first and second moments of a binomial row:

1. `sum_range_mul_choose` — the first moment
        ∑_{k=0}^{n} k · C(n,k) = n · 2ⁿ⁻¹ .

2. `sum_range_sq_mul_choose` — the second moment
        ∑_{k=0}^{n} k² · C(n,k) = n · (n+1) · 2ⁿ⁻² .

Probabilistically these say that a `Binomial(n, ½)` variable has mean `n/2`
(divide the first identity by `2ⁿ`) and second moment `n(n+1)/4`, hence variance
`n/4`.  Combinatorially, `∑ k·C(n,k)` counts the pairs *(committee, chair)* drawn
from `n` people: choose the chair `n` ways, then any subset of the rest, giving
`n·2ⁿ⁻¹`.

## Method

Everything reduces to Mathlib's **absorption identity** `Nat.succ_mul_choose_eq`,

        (n+1) · C(n,k) = C(n+1, k+1) · (k+1),

which we repackage as `absorb : (k+1) · C(n+1, k+1) = (n+1) · C(n,k)`.  Peeling the
`k = 0` term with `Finset.sum_range_succ'` and applying `absorb` turns a weighted
sum over row `n+1` into `(n+1)` times an *un*weighted sum over row `n`, which
`Nat.sum_range_choose` evaluates to `2ⁿ`.  The second moment writes `k² = k·k`,
applies `absorb` once, and then reuses the first-moment identity together with the
row sum.  Stating the lemmas in the shifted forms `n+2` / `n+3` keeps everything
inside ℕ with no truncated subtraction; the classic `n·2ⁿ⁻¹` / `n(n+1)·2ⁿ⁻²`
statements are recovered as corollaries.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ09

open Finset

/-- **Absorption identity (repackaged).**
    `(k+1) · C(n+1, k+1) = (n+1) · C(n, k)` — pull a factor `k+1` out of a binomial
    coefficient and trade it for the row index `n+1`.  This is
    `Nat.add_one_mul_choose_eq` with the two sides commuted. -/
theorem absorb (n k : ℕ) :
    (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
  rw [Nat.add_one_mul_choose_eq]; ring

-- ============================================================
-- First moment
-- ============================================================

/-- **First moment (shifted form).**
    `∑_{k=0}^{n+1} k · C(n+1, k) = (n+1) · 2ⁿ`. -/
theorem sum_range_succ_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 2), k * (n + 1).choose k = (n + 1) * 2 ^ n := by
  rw [Finset.sum_range_succ' (fun k => k * (n + 1).choose k) (n + 1)]
  simp only [zero_mul, add_zero]
  rw [Finset.sum_congr rfl (fun k _ => absorb n k), ← Finset.mul_sum,
      Nat.sum_range_choose]

/-- **First moment of a binomial row.**
    `∑_{k=0}^{n} k · C(n,k) = n · 2ⁿ⁻¹`. -/
theorem sum_range_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * n.choose k = n * 2 ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ m => simpa using sum_range_succ_mul_choose m

-- ============================================================
-- Second moment
-- ============================================================

/-- **Second moment (shifted form).**
    `∑_{k=0}^{n+2} k² · C(n+2, k) = (n+2)·(n+3) · 2ⁿ`. -/
theorem sum_range_succ_succ_sq_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 3), k ^ 2 * (n + 2).choose k = (n + 2) * (n + 3) * 2 ^ n := by
  rw [Finset.sum_range_succ' (fun k => k ^ 2 * (n + 2).choose k) (n + 2)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
  -- ∑ k ∈ range (n+2), (k+1)² · C(n+2, k+1) = (n+2)·(n+3)·2ⁿ
  have hterm : ∀ k ∈ range (n + 2),
      (k + 1) ^ 2 * (n + 2).choose (k + 1) = (n + 2) * ((k + 1) * (n + 1).choose k) := by
    intro k _
    have hab : (k + 1) * (n + 2).choose (k + 1) = (n + 2) * (n + 1).choose k := absorb (n + 1) k
    rw [pow_two, mul_assoc, hab]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- (n+2) · ∑ (k+1)·C(n+1,k) = (n+2)·(n+3)·2ⁿ
  have hsplit : ∑ k ∈ range (n + 2), (k + 1) * (n + 1).choose k
      = (∑ k ∈ range (n + 2), k * (n + 1).choose k)
        + ∑ k ∈ range (n + 2), (n + 1).choose k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsplit, sum_range_succ_mul_choose, Nat.sum_range_choose]
  ring

/-- **Second moment of a binomial row.**
    `∑_{k=0}^{n} k² · C(n,k) = n · (n+1) · 2ⁿ⁻²`  (for `n ≥ 2`). -/
theorem sum_range_sq_mul_choose (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range (n + 1), k ^ 2 * n.choose k = n * (n + 1) * 2 ^ (n - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : 2 + m - 2 = m := by omega
  have e2 : 2 + m + 1 = m + 3 := by omega
  have e3 : 2 + m = m + 2 := by omega
  rw [e, e3]
  simpa [e2] using sum_range_succ_succ_sq_mul_choose m

-- ============================================================
-- Sanity checks
-- ============================================================

/-- `∑ k·C(4,k) = 0+4+24+48+32 = 4·2³ = 32`. -/
example : ∑ k ∈ range 5, k * (4 : ℕ).choose k = 4 * 2 ^ 3 := by decide

/-- `∑ k²·C(4,k) = 0+4+48+144+128 = 4·5·2² = 80`. -/
example : ∑ k ∈ range 5, k ^ 2 * (4 : ℕ).choose k = 4 * 5 * 2 ^ 2 := by decide

end CombinationsFormulaOQ09
