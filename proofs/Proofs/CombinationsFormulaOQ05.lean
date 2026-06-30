import Mathlib

/-
# The Alternating Row Sum of Pascal's Triangle and the Even/Odd Split

## Open Question OQ-05

For `n ≥ 1`, the alternating sum of the `n`-th row of Pascal's triangle vanishes:

  ∑_{k=0}^{n} (-1)^k · C(n, k) = 0 .

Mathlib provides this as `Int.alternating_sum_range_choose_of_ne`.  Standing
alone it is a one-line corollary, so this file develops its genuine
combinatorial content: combined with the total row sum
`∑_{k} C(n, k) = 2^n` (`Nat.sum_range_choose`), the vanishing alternating sum
says the even-indexed and odd-indexed binomial coefficients contribute equally.

1. `alternating_sum_choose_eq_zero` — anchor: `∑ (-1)^k C(n,k) = 0` for `n ≥ 1`.

2. `sum_even_choose_eq_sum_odd_choose` — the even/odd split:
        ∑_{k even} C(n, k) = ∑_{k odd} C(n, k)   (n ≥ 1).

3. `sum_even_choose` — each half is exactly `2^{n-1}`:
        ∑_{k even} C(n, k) = 2^{n-1}             (n ≥ 1).

## Mathematical Context

The two fundamental row identities of Pascal's triangle are the total sum
`∑ C(n,k) = 2^n` (number of all subsets) and the alternating sum
`∑ (-1)^k C(n,k) = 0` (subsets of even size minus subsets of odd size).
Together they are equivalent to the statement that an `n`-element set with
`n ≥ 1` has equally many even-sized and odd-sized subsets, each numbering
`2^{n-1}`.  This is the simplest instance of the inclusion–exclusion
cancellation that underlies the binomial transform.

The proof splits the row sum over the even/odd parity of the index using
`Finset.sum_filter_add_sum_filter_not`, evaluating `(-1)^k` as `+1` on even
indices (`Even.neg_one_pow`) and `-1` on odd indices (`Odd.neg_one_pow`).

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ05

open Finset

/-- **Anchor.** The alternating row sum of Pascal's triangle vanishes for `n ≥ 1`.
    This is `Int.alternating_sum_range_choose_of_ne`. -/
theorem alternating_sum_choose_eq_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ Finset.range (n + 1), ((-1) ^ k * n.choose k : ℤ) = 0 :=
  Int.alternating_sum_range_choose_of_ne hn

/-- **Even/odd split.** For `n ≥ 1` the even-indexed and odd-indexed binomial
    coefficients of row `n` have equal sums. -/
theorem sum_even_choose_eq_sum_odd_choose {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Odd k), (n.choose k : ℤ) := by
  have key := alternating_sum_choose_eq_zero hn
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) (fun k => Even k)
        (fun k => ((-1) ^ k * n.choose k : ℤ))] at key
  -- Evaluate (-1)^k on the even part (= +1) and the odd part (= -1).
  have hE : ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Even k),
      ((-1) ^ k * n.choose k : ℤ)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_filter] at hk
    rw [hk.2.neg_one_pow, one_mul]
  have hO : ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Even k),
      ((-1) ^ k * n.choose k : ℤ)
      = - ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Odd k), (n.choose k : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr ?_ fun k hk => ?_
    · simp only [Nat.not_even_iff_odd]
    · rw [Finset.mem_filter] at hk
      rw [hk.2.neg_one_pow, neg_one_mul]
  rw [hE, hO] at key
  linarith

/-- The total row sum, cast to `ℤ`: `∑ C(n,k) = 2^n`. -/
private theorem sum_choose_int (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) = 2 ^ n := by
  exact_mod_cast Nat.sum_range_choose n

/-- **Each half equals `2^{n-1}`.** For `n ≥ 1`,
    `∑_{k even} C(n, k) = 2^{n-1}`. -/
theorem sum_even_choose {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ)
      = 2 ^ (n - 1) := by
  have hEO := sum_even_choose_eq_sum_odd_choose hn
  have hsplit :
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => Even k), (n.choose k : ℤ))
        + (∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ))
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [sum_choose_int] at hsplit
  -- rewrite the ¬Even filter as Odd, then use even = odd
  have hodd_filter :
      (Finset.range (n + 1)).filter (fun k => ¬ Even k)
        = (Finset.range (n + 1)).filter (fun k => Odd k) := by
    simp only [Nat.not_even_iff_odd]
  rw [hodd_filter, ← hEO] at hsplit
  -- hsplit : E + E = 2^n, i.e. 2*E = 2^n; and 2^n = 2 * 2^(n-1)
  have hpow : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  linarith

/-- Sanity check (row 4): even part `C(4,0)+C(4,2)+C(4,4) = 1+6+1 = 8 = 2^3`. -/
example :
    ∑ k ∈ (Finset.range 5).filter (fun k => Even k), (Nat.choose 4 k : ℤ) = 8 := by
  decide

end CombinationsFormulaOQ05
