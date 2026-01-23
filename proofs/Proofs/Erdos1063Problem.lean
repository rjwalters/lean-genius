/-
Erdős Problem #1063: Binomial Divisibility by Almost All n-i

**Statement**: Let k ≥ 2. Define n_k ≥ 2k to be the least n such that
(n-i) | C(n,k) for all but one 0 ≤ i < k. Estimate n_k.

**Status**: OPEN (exact behavior of n_k unknown)

**Known Results**:
- Erdős-Selfridge: If n ≥ 2k, at least one 0 ≤ i < k does NOT divide C(n,k)
- Small values: n_2=4, n_3=6, n_4=9, n_5=12
- Upper bound (Monier): n_k ≤ k! for k ≥ 3
- Improved: n_k ≤ k · lcm(2,...,k-1) ≤ e^{(1+o(1))k}

Reference: https://erdosproblems.com/1063
Problem B31 in Guy's "Unsolved Problems in Number Theory"
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos1063

/-
## Part I: Basic Definitions
-/

/-- Count of 0 ≤ i < k such that (n-i) | C(n,k). -/
def divisorCount (n k : ℕ) : ℕ :=
  (Finset.range k).filter (fun i => (n - i) ∣ n.choose k) |>.card

/-- n satisfies the "all but one" condition: exactly k-1 values of i work. -/
def allButOne (n k : ℕ) : Prop :=
  divisorCount n k = k - 1

/-- n_k: the smallest n ≥ 2k with the "all but one" property. -/
noncomputable def n_k (k : ℕ) : ℕ :=
  if h : k ≥ 2 then
    Nat.find ⟨k.factorial, by sorry⟩  -- Monier's upper bound existence
  else 0

/-
## Part II: The Erdős-Selfridge Theorem
-/

/-- Erdős-Selfridge: For n ≥ 2k, at least one 0 ≤ i < k fails to divide C(n,k).
    This is why we look for "all but one" rather than "all". -/
axiom erdos_selfridge_bound (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 2 * k) :
    divisorCount n k < k

/-- Equivalently: there exists some i that doesn't divide. -/
theorem exists_non_divisor (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 2 * k) :
    ∃ i < k, ¬(n - i) ∣ n.choose k := by
  have h := erdos_selfridge_bound n k hk hn
  by_contra hall
  push_neg at hall
  have : divisorCount n k = k := by
    unfold divisorCount
    simp only [Finset.filter_eq_self, Finset.mem_range]
    exact hall
  omega

/-
## Part III: Small Values
-/

/-- n_2 = 4: C(4,2) = 6. Divisible by 4, 3, but not 2 (wait, 2|6). Actually:
    4-0=4, 4|6? No. 4-1=3, 3|6? Yes. So only one divides.
    Actually need to re-verify... -/
-- Let's compute: C(4,2) = 6
-- 4-0 = 4: 4 ∤ 6 (6/4 not integer)
-- 4-1 = 3: 3 | 6 ✓
-- So divisorCount 4 2 = 1 = 2-1 ✓

example : Nat.choose 4 2 = 6 := by native_decide
example : ¬(4 ∣ 6) := by native_decide
example : 3 ∣ 6 := by native_decide

theorem n2_is_4 : n_k 2 = 4 := by sorry

/-- n_3 = 6: C(6,3) = 20. Check 6,5,4.
    6-0=6: 6 ∤ 20
    6-1=5: 5 | 20 ✓
    6-2=4: 4 | 20 ✓
    divisorCount = 2 = 3-1 ✓ -/
example : Nat.choose 6 3 = 20 := by native_decide
example : ¬(6 ∣ 20) := by native_decide
example : 5 ∣ 20 := by native_decide
example : 4 ∣ 20 := by native_decide

theorem n3_is_6 : n_k 3 = 6 := by sorry

/-- n_4 = 9: C(9,4) = 126. Check 9,8,7,6.
    9-0=9: 9 | 126 ✓ (126 = 14·9)
    9-1=8: 8 ∤ 126
    9-2=7: 7 | 126 ✓ (126 = 18·7)
    9-3=6: 6 | 126 ✓ (126 = 21·6)
    divisorCount = 3 = 4-1 ✓ -/
example : Nat.choose 9 4 = 126 := by native_decide
example : 9 ∣ 126 := by native_decide
example : ¬(8 ∣ 126) := by native_decide
example : 7 ∣ 126 := by native_decide
example : 6 ∣ 126 := by native_decide

theorem n4_is_9 : n_k 4 = 9 := by sorry

/-- n_5 = 12: C(12,5) = 792. Check 12,11,10,9,8.
    12: 12 | 792 ✓ (792 = 66·12)
    11: 11 | 792 ✓ (792 = 72·11)
    10: 10 ∤ 792 (792/10 = 79.2)
    9: 9 | 792 ✓ (792 = 88·9)
    8: 8 | 792 ✓ (792 = 99·8)
    divisorCount = 4 = 5-1 ✓ -/
example : Nat.choose 12 5 = 792 := by native_decide
example : 12 ∣ 792 := by native_decide
example : 11 ∣ 792 := by native_decide
example : ¬(10 ∣ 792) := by native_decide
example : 9 ∣ 792 := by native_decide
example : 8 ∣ 792 := by native_decide

theorem n5_is_12 : n_k 5 = 12 := by sorry

/-- The known small values. -/
axiom small_values : n_k 2 = 4 ∧ n_k 3 = 6 ∧ n_k 4 = 9 ∧ n_k 5 = 12

/-
## Part IV: Upper Bounds
-/

/-- Monier's bound: n_k ≤ k! for k ≥ 3.
    Because C(k!,k) is divisible by k!-i for 1 ≤ i < k. -/
axiom monier_bound (k : ℕ) (hk : k ≥ 3) : n_k k ≤ k.factorial

/-- Improved bound: n_k ≤ k · lcm(2,...,k-1). -/
axiom improved_bound (k : ℕ) (hk : k ≥ 3) :
    n_k k ≤ k * (Finset.Icc 2 (k - 1)).lcm id

/-- The improved bound grows like e^{(1+o(1))k}. -/
axiom improved_bound_asymptotic :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
      (n_k k : ℝ) ≤ Real.exp ((1 + ε) * k)

/-
## Part V: Lower Bounds and Open Questions
-/

/-- Basic lower bound: n_k ≥ 2k (by definition). -/
theorem n_k_ge_2k (k : ℕ) (hk : k ≥ 2) : n_k k ≥ 2 * k := by
  sorry

/-- The main open question: What is the growth rate of n_k?
    Is it polynomial? Exponential? What's the exact constant in e^{ck}? -/
def mainQuestion : Prop :=
  ∃ c : ℝ, c > 0 ∧
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (n_k k : ℝ) ≥ Real.exp ((c - ε) * k)) ∧
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, (n_k k : ℝ) ≤ Real.exp ((c + ε) * k))

/-
## Part VI: Summary
-/

/-- Erdős Problem #1063: Summary

    **Definition**: n_k = least n ≥ 2k with (n-i) | C(n,k) for exactly k-1 values of i.

    **Background**: Erdős-Selfridge showed at least one i fails, so "all but one" is best possible.

    **Known**: n_2=4, n_3=6, n_4=9, n_5=12

    **Bounds**:
    - Lower: n_k ≥ 2k (definition)
    - Upper: n_k ≤ k · lcm(2,...,k-1) ≤ e^{(1+o(1))k}

    **Open**: Exact growth rate of n_k. -/
theorem erdos_1063_summary :
    -- Small values exist
    (n_k 2 = 4 ∧ n_k 3 = 6 ∧ n_k 4 = 9 ∧ n_k 5 = 12) ∧
    -- Upper bound exists
    (∀ k ≥ 3, n_k k ≤ k.factorial) := by
  exact ⟨small_values, monier_bound⟩

end Erdos1063
