/-
# Combinatorial Moments of the Binomial Coefficients (OQ-03-OQ-01)

Research Question (follow-up to OQ-03 "Binomial Distribution from the Binomial
Theorem"): the parent derives the *probabilistic* moments of the binomial
distribution over ℝ — the mean `E[X] = np` and the variance `np(1-p)` — by
weighting `C(n,k)` with `pᵏ(1-p)ⁿ⁻ᵏ`.  What are the *unweighted* combinatorial
moments, i.e. the closed forms of the plain integer sums

    Σ_{k=0}^{n} k · C(n,k),   Σ_{k=0}^{n} k(k-1) · C(n,k),   Σ_{k=0}^{n} k² · C(n,k) ?

These are the `p = 1` / counting analogues of the probabilistic moments, and
they are NOT in Mathlib (Mathlib has `Nat.sum_range_choose : Σ C(n,k) = 2ⁿ`
— the zeroth moment — but none of the higher ones).

Answer.  All three have clean closed forms, obtained from the single
*absorption* identity `(k+1)·C(n+1,k+1) = (n+1)·C(n,k)` (already proved in the
parent) together with the zeroth-moment `Σ C(n,k) = 2ⁿ`:

    Σ k · C(n,k)      = n · 2ⁿ⁻¹
    Σ k(k-1) · C(n,k) = n(n-1) · 2ⁿ⁻²
    Σ k² · C(n,k)     = n(n+1) · 2ⁿ⁻²

The mechanism is exactly the `xⁿ ↦ derivative at x=1` of `(1+x)ⁿ = Σ C(n,k)xᵏ`,
done purely combinatorially over ℕ (no analysis, no casts).  Subtraction-free
"successor" forms are proved first to keep everything inside ℕ, then the
headline forms with `2ⁿ⁻¹` / `2ⁿ⁻²` follow.

Tags: combinatorics, binomial-coefficients, moments, absorption, generating-functions
-/

import Mathlib
import Proofs.BinomialTheoremOQ03

open Finset BigOperators

namespace BinomialTheoremOQ03OQ01

/-! ## Part I: First combinatorial moment  Σ k·C(n,k) = n·2ⁿ⁻¹ -/

/-- Subtraction-free form of the first moment.  Summing `k·C(n+1,k)` over the
full range `0 ≤ k ≤ n+1` gives `(n+1)·2ⁿ`.  Proved by peeling the vanishing
`k = 0` term, reindexing `k ↦ k+1`, and applying absorption term-by-term to
collapse the sum to `(n+1)·Σ C(n,k) = (n+1)·2ⁿ`. -/
theorem sum_id_mul_choose_succ (n : ℕ) :
    ∑ k ∈ range (n + 2), k * (n + 1).choose k = (n + 1) * 2 ^ n := by
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_mul, add_zero]
  -- goal: Σ x ∈ range (n+1), (x+1) * C(n+1, x+1) = (n+1) * 2^n
  rw [← Nat.sum_range_choose n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  -- (k+1) * C(n+1, k+1) = (n+1) * C(n, k)
  exact BinomialTheoremOQ03.absorption n k

/-- **First combinatorial moment.**  `Σ_{k=0}^{n} k · C(n,k) = n · 2ⁿ⁻¹`.
This is the counting (`p = 1`) analogue of the binomial mean `E[X] = np`. -/
theorem sum_id_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * n.choose k = n * 2 ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ m => simpa using sum_id_mul_choose_succ m

/-! ## Part II: Second factorial moment  Σ k(k-1)·C(n,k) = n(n-1)·2ⁿ⁻² -/

/-- Subtraction-free form of the second factorial moment.  Summing
`k(k-1)·C(n+2,k)` over `0 ≤ k ≤ n+2` gives `(n+2)(n+1)·2ⁿ`.  Two vanishing
terms (`k = 0, 1`) are peeled, the index is shifted `k ↦ k+2`, and double
absorption collapses the result to `(n+2)(n+1)·Σ C(n,k)`. -/
theorem sum_descFactorial_mul_choose_succ (n : ℕ) :
    ∑ k ∈ range (n + 3), k * (k - 1) * (n + 2).choose k
      = (n + 2) * (n + 1) * 2 ^ n := by
  -- peel k = 0 (term is 0·(0-1)·… = 0)
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_mul, Nat.zero_sub, Nat.mul_zero, add_zero]
  -- now Σ x ∈ range (n+2), (x+1)·((x+1)-1)·C(n+2, x+1)
  rw [show n + 2 = (n + 1) + 1 from rfl, Finset.sum_range_succ']
  -- peel the new k = 0 (i.e. original k = 1: term is 1·0·… = 0)
  simp only [Nat.add_sub_cancel, Nat.zero_add,
    Nat.sub_self, Nat.mul_zero, Nat.zero_mul, add_zero]
  -- goal: Σ x ∈ range (n+1), (x+2)·(x+1)·C(n+2, x+2) = (n+2)(n+1)·2^n
  rw [← Nat.sum_range_choose n, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  -- (k+2)(k+1)·C(n+2, k+2) = (n+2)(n+1)·C(n, k)
  have h := BinomialTheoremOQ03.double_absorption n k
  -- normalise the literal `+ 1 + 1` shapes produced by reindexing
  simpa [Nat.add_sub_cancel] using h

/-- **Second factorial moment.**  `Σ_{k=0}^{n} k(k-1) · C(n,k) = n(n-1) · 2ⁿ⁻²`.
This is the counting analogue of `E[X(X-1)] = n(n-1)p²` from the parent. -/
theorem sum_descFactorial_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * (k - 1) * n.choose k = n * (n - 1) * 2 ^ (n - 2) := by
  match n with
  | 0 => simp
  | 1 => decide
  | (m + 2) => simpa using sum_descFactorial_mul_choose_succ m

/-! ## Part III: Second moment  Σ k²·C(n,k) = n(n+1)·2ⁿ⁻² -/

/-- The pointwise splitting `k² = k(k-1) + k`, valid for *all* `k : ℕ`
(including `k = 0`, where truncated subtraction gives `0·0 + 0 = 0`). -/
theorem sq_eq_descFactorial_add_id (k : ℕ) : k ^ 2 = k * (k - 1) + k := by
  cases k with
  | zero => rfl
  | succ j => simp only [Nat.add_sub_cancel, pow_two]; ring

/-- Subtraction-free form of the second moment:
`Σ k²·C(n+2,k) = (n+2)(n+3)·2ⁿ`.  Obtained by splitting `k² = k(k-1) + k` and
adding the first moment to the second factorial moment. -/
theorem sum_sq_mul_choose_succ (n : ℕ) :
    ∑ k ∈ range (n + 3), k ^ 2 * (n + 2).choose k = (n + 2) * (n + 3) * 2 ^ n := by
  have hsplit : ∑ k ∈ range (n + 3), k ^ 2 * (n + 2).choose k
      = (∑ k ∈ range (n + 3), k * (k - 1) * (n + 2).choose k)
        + ∑ k ∈ range (n + 3), k * (n + 2).choose k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [sq_eq_descFactorial_add_id k, Nat.add_mul]
  rw [hsplit, sum_descFactorial_mul_choose_succ n]
  -- the first moment over range (n+3) is `sum_id_mul_choose_succ (n+1)`
  have hfirst := sum_id_mul_choose_succ (n + 1)
  rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at hfirst
  rw [hfirst]
  ring

/-- **Second combinatorial moment.**  `Σ_{k=0}^{n} k² · C(n,k) = n(n+1) · 2ⁿ⁻²`
for `n ≥ 2`.  This is the counting analogue of `E[X²] = n(n-1)p² + np`; the
variance identity `Var = E[X²] - E[X]²` of the parent corresponds to
`n(n+1)2ⁿ⁻² - (n·2ⁿ⁻¹)²/2ⁿ`.  The hypothesis `2 ≤ n` is genuinely needed: at
`n = 1` the left side is `1` but truncated subtraction makes `2¹⁻² = 2⁰ = 1`,
giving `1·2·1 = 2 ≠ 1` (the same reason the parent's variance requires `n ≥ 2`);
the subtraction-free `sum_sq_mul_choose_succ` holds for every `n`. -/
theorem sum_sq_mul_choose (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range (n + 1), k ^ 2 * n.choose k = n * (n + 1) * 2 ^ (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using sum_sq_mul_choose_succ m

/-! ## Part IV: Sanity checks -/

example : ∑ k ∈ range 5, k * (4).choose k = 4 * 2 ^ 3 := by decide
example : ∑ k ∈ range 5, k ^ 2 * (4).choose k = 4 * 5 * 2 ^ 2 := by decide
example : ∑ k ∈ range 6, k * (k - 1) * (5).choose k = 5 * 4 * 2 ^ 3 := by decide

end BinomialTheoremOQ03OQ01
