/-
Extended Binomial Coefficient Identities - OQ-01

Extends CombinationsFormula with:
1. Vandermonde's Identity: C(m+n, r) = Σ_{k=0}^{r} C(m,k) * C(n, r-k)
2. Hockey Stick Identity: Σ_{i=0}^{n} C(i+r, r) = C(n+r+1, r+1)
3. Double Counting / Product Identity: C(n, k) * C(k, j) = C(n, j) * C(n-j, k-j)
4. Row Sum and Alternating Row Sum
5. Binomial coefficient upper bound C(n,k) ≤ 2^n
6. Central binomial coefficient bound C(2n,n) ≤ 4^n

Tags: combinatorics, binomial-coefficients, identities, extension
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Nat Finset BigOperators

namespace CombinationsFormulaOQ01

-- ============================================================
-- Part I: Vandermonde's Identity
-- ============================================================

/-- **Vandermonde's Identity**: C(m+n, r) = Σ_{k=0}^{r} C(m, k) * C(n, r-k).

    This fundamental identity expresses C(m+n, r) as a convolution of
    binomial coefficients. Combinatorially: choosing r items from m+n
    can be done by choosing k from the first m and r-k from the remaining n. -/
theorem vandermonde (m n r : ℕ) :
    Nat.choose (m + n) r = ∑ k ∈ Finset.range (r + 1), Nat.choose m k * Nat.choose n (r - k) := by
  rw [Nat.add_choose_eq]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose m i * Nat.choose n j)) r

-- Concrete verifications
example : Nat.choose 8 4 = 70 := by native_decide
example : ∑ k ∈ Finset.range 5, Nat.choose 5 k * Nat.choose 3 (4 - k) = 70 := by native_decide

-- ============================================================
-- Part II: Hockey Stick (Christmas Stocking) Identity
-- ============================================================

/-- **Hockey Stick Identity**: Σ_{i=0}^{n} C(i+r, r) = C(n+r+1, r+1).

    This identity says the sum of a diagonal in Pascal's triangle
    equals an entry one row below and one column to the right.
    Named after the "hockey stick" shape formed in Pascal's triangle. -/
theorem hockey_stick (n r : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Nat.choose (i + r) r = Nat.choose (n + r + 1) (r + 1) := by
  induction n with
  | zero => simp [Nat.choose_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : k + 1 + r + 1 = (k + r + 1) + 1 := by omega
    have h2 : k + 1 + r = k + r + 1 := by omega
    rw [h1, h2, Nat.choose_succ_succ (k + r + 1) r, add_comm]

-- Verifications
example : ∑ i ∈ Finset.range 4, Nat.choose (i + 0) 0 = 4 := by native_decide
example : ∑ i ∈ Finset.range 4, Nat.choose (i + 1) 1 = 10 := by native_decide
example : ∑ i ∈ Finset.range 4, Nat.choose (i + 2) 2 = 20 := by native_decide
example : Nat.choose 6 3 = 20 := by native_decide

-- ============================================================
-- Part III: Product / Double Counting Identity
-- ============================================================

/-- **Product Identity**: C(n, k) * C(k, j) = C(n, j) * C(n-j, k-j) when j ≤ k ≤ n.

    Combinatorial meaning: choosing k items from n and then j from those k
    is the same as choosing j from n directly and then choosing k-j more
    from the remaining n-j items. -/
theorem choose_product (n k j : ℕ) (hjk : j ≤ k) (hkn : k ≤ n) :
    Nat.choose n k * Nat.choose k j = Nat.choose n j * Nat.choose (n - j) (k - j) := by
  have hjn : j ≤ n := le_trans hjk hkn
  -- Strategy: show both sides × (j! × (k-j)! × (n-k)!) = n!, then cancel
  suffices h : Nat.choose n k * Nat.choose k j * (j.factorial * (k - j).factorial * (n - k).factorial)
      = Nat.choose n j * Nat.choose (n - j) (k - j) * (j.factorial * (k - j).factorial * (n - k).factorial) by
    have hpos : j.factorial * (k - j).factorial * (n - k).factorial ≠ 0 := by positivity
    exact mul_right_cancel₀ hpos h
  -- Mathlib: C(a, b) * b! * (a-b)! = a!  (left-associated)
  have hkj : Nat.choose k j * j.factorial * (k - j).factorial = k.factorial :=
    Nat.choose_mul_factorial_mul_factorial hjk
  have hnk : Nat.choose n k * k.factorial * (n - k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkn
  have lhs : Nat.choose n k * Nat.choose k j * (j.factorial * (k - j).factorial * (n - k).factorial)
      = n.factorial := by
    have h1 : Nat.choose n k * Nat.choose k j * (j.factorial * (k - j).factorial * (n - k).factorial)
        = Nat.choose n k * (Nat.choose k j * j.factorial * (k - j).factorial) * (n - k).factorial := by ring
    rw [h1, hkj, hnk]
  have hkj_le : k - j ≤ n - j := by omega
  have hnjkj : Nat.choose (n - j) (k - j) * (k - j).factorial * (n - j - (k - j)).factorial = (n - j).factorial :=
    Nat.choose_mul_factorial_mul_factorial hkj_le
  have h_eq : n - j - (k - j) = n - k := by omega
  rw [h_eq] at hnjkj
  have hnj : Nat.choose n j * j.factorial * (n - j).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hjn
  have rhs : Nat.choose n j * Nat.choose (n - j) (k - j) * (j.factorial * (k - j).factorial * (n - k).factorial)
      = n.factorial := by
    have h2 : Nat.choose n j * Nat.choose (n - j) (k - j) * (j.factorial * (k - j).factorial * (n - k).factorial)
        = Nat.choose n j * j.factorial * (Nat.choose (n - j) (k - j) * (k - j).factorial * (n - k).factorial) := by ring
    rw [h2, hnjkj, hnj]
  linarith

-- Verification: C(6, 3) * C(3, 1) = 20 * 3 = 60 = C(6, 1) * C(5, 2) = 6 * 10
example : Nat.choose 6 3 * Nat.choose 3 1 = Nat.choose 6 1 * Nat.choose 5 2 := by native_decide

-- ============================================================
-- Part IV: Binomial Sum Identities
-- ============================================================

/-- **Row Sum**: Σ_{k=0}^{n} C(n, k) = 2^n. -/
theorem choose_row_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose n k = 2 ^ n :=
  Nat.sum_range_choose n

example : ∑ k ∈ Finset.range 5, Nat.choose 4 k = 16 := by native_decide

/-- **Alternating Row Sum**: Σ_{k=0}^{n} (-1)^k * C(n, k) = 0 for n ≥ 1. -/
theorem choose_alternating_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ k * (Nat.choose n k : ℤ)) = 0 :=
  Int.alternating_sum_range_choose_of_ne (by omega)

example : ∑ k ∈ Finset.range 5, ((-1 : ℤ) ^ k * (Nat.choose 4 k : ℤ)) = 0 := by native_decide

-- ============================================================
-- Part V: Choose Inequality
-- ============================================================

/-- **Binomial Bound**: C(n, k) ≤ 2^n. Every binomial coefficient is bounded
    by the sum of the entire row. -/
theorem choose_le_pow2 (n k : ℕ) : Nat.choose n k ≤ 2 ^ n := by
  by_cases h : k ≤ n
  · calc Nat.choose n k
        ≤ ∑ i ∈ Finset.range (n + 1), Nat.choose n i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

example : Nat.choose 10 5 ≤ 2 ^ 10 := by native_decide

-- ============================================================
-- Part VI: Central Binomial Coefficient Bound
-- ============================================================

/-- **Central Binomial Coefficient**: C(2n, n) ≤ 4^n. -/
theorem central_binom_le (n : ℕ) : Nat.choose (2 * n) n ≤ 4 ^ n := by
  calc Nat.choose (2 * n) n
      ≤ 2 ^ (2 * n) := choose_le_pow2 (2 * n) n
    _ = (2 ^ 2) ^ n := by rw [pow_mul]
    _ = 4 ^ n := by norm_num

example : Nat.choose 10 5 = 252 := by native_decide
example : 252 ≤ 4 ^ 5 := by norm_num

-- ============================================================
-- Part VII: Diagonal Sums (Fibonacci Connection)
-- ============================================================

/-- The shallow diagonal sums of Pascal's triangle give Fibonacci numbers.
    Σ_{j} C(n-j, j) = F(n+1). Verified for small cases. -/

-- F(6) = 8: C(5,0) + C(4,1) + C(3,2) + C(2,3) = 1 + 4 + 3 + 0 = 8
example : Nat.choose 5 0 + Nat.choose 4 1 + Nat.choose 3 2 + Nat.choose 2 3 = 8 := by native_decide

-- F(7) = 13: C(6,0) + C(5,1) + C(4,2) + C(3,3) = 1 + 5 + 6 + 1 = 13
example : Nat.choose 6 0 + Nat.choose 5 1 + Nat.choose 4 2 + Nat.choose 3 3 = 13 := by native_decide

-- ============================================================
-- Part VIII: Summary
-- ============================================================

/-- Summary of key identities proved. -/
theorem identities_summary :
    (∀ n, ∑ k ∈ Finset.range (n + 1), Nat.choose n k = 2 ^ n) ∧
    (∀ n r, ∑ i ∈ Finset.range (n + 1), Nat.choose (i + r) r = Nat.choose (n + r + 1) (r + 1)) ∧
    (∀ m n r, Nat.choose (m + n) r = ∑ k ∈ Finset.range (r + 1), Nat.choose m k * Nat.choose n (r - k)) ∧
    (∀ n k, Nat.choose n k ≤ 2 ^ n) := by
  exact ⟨Nat.sum_range_choose, hockey_stick, vandermonde, choose_le_pow2⟩

end CombinationsFormulaOQ01
