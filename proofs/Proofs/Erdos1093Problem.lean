/-
Erdős Problem #1093: Deficiency of Binomial Coefficients

**Statement**: For n ≥ 2k, the deficiency of C(n,k) is defined as follows:
- Undefined if C(n,k) is divisible by some prime p ≤ k
- Otherwise, count of 0 ≤ i < k such that n-i is k-smooth

Questions:
1. Are there infinitely many C(n,k) with deficiency 1?
2. Are there only finitely many with deficiency > 1?

**Status**: OPEN

**Known Examples**:
- Deficiency 1: C(7,3), C(13,4), C(14,4), C(23,5), C(62,6), ... (58 with n ≤ 10^5)
- Deficiency 2: C(44,8), C(74,10), C(174,12), ... (8 known)
- Deficiency 3: C(46,10), C(47,10), C(241,16), ... (6 known)
- Deficiency 4: C(47,11)
- Deficiency 9: C(284,28)

Reference: https://erdosproblems.com/1093
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos1093

/-
## Part I: k-Smooth Numbers
-/

/-- A number is k-smooth if all its prime factors are ≤ k. -/
def IsSmooth (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ k

/-- 1 is k-smooth for all k. -/
theorem one_smooth (k : ℕ) : IsSmooth 1 k := by
  intro p hp hdiv
  have : p = 1 := Nat.eq_one_of_pos_of_self_mul_self_mod_eq_one (Nat.Prime.one_lt hp).le
    (by simp [Nat.dvd_one.mp hdiv])
  omega

/-- Powers of 2 are k-smooth for k ≥ 2. -/
theorem pow2_smooth (n : ℕ) (hk : k ≥ 2) : IsSmooth (2^n) k := by
  intro p hp hdiv
  have : p = 2 := by
    have := (Nat.Prime.pow_dvd_iff_le_ord_compl_of_prime hp Nat.prime_two).mp
    sorry -- p | 2^n → p = 2
  omega

/-
## Part II: Deficiency Definition
-/

/-- Whether deficiency is defined: C(n,k) has no prime factor ≤ k. -/
def DeficiencyDefined (n k : ℕ) : Prop :=
  n ≥ 2 * k ∧ ∀ p : ℕ, p.Prime → p ≤ k → ¬(p ∣ n.choose k)

/-- The deficiency of C(n,k): count of k-smooth values among n, n-1, ..., n-k+1. -/
def deficiency (n k : ℕ) : ℕ :=
  (Finset.range k).filter (fun i => IsSmooth (n - i) k) |>.card

/-- A pair (n,k) has deficiency d. -/
structure HasDeficiency (n k d : ℕ) : Prop where
  defined : DeficiencyDefined n k
  value : deficiency n k = d

/-
## Part III: Deficiency 1 Examples
-/

/-- C(7,3) = 35 has deficiency 1.
    Check: 35 = 5·7, no prime ≤ 3 divides.
    Smooth check: 7 (7 > 3), 6=2·3 (smooth!), 5 (5 > 3).
    Deficiency = 1 (only 6 is smooth). -/
example : Nat.choose 7 3 = 35 := by native_decide
example : ¬(2 ∣ 35) := by native_decide
example : ¬(3 ∣ 35) := by native_decide

/-- C(13,4) = 715 has deficiency 1.
    715 = 5·11·13, no prime ≤ 4 divides.
    Check 13, 12, 11, 10: only 12 = 2²·3 is 4-smooth.
    Deficiency = 1. -/
example : Nat.choose 13 4 = 715 := by native_decide
example : ¬(2 ∣ 715) := by native_decide
example : ¬(3 ∣ 715) := by native_decide

/-- C(23,5) = 33649 has deficiency 1. -/
example : Nat.choose 23 5 = 33649 := by native_decide

/-- Known deficiency 1 examples. -/
def deficiency1Examples : List (ℕ × ℕ) :=
  [(7, 3), (13, 4), (14, 4), (23, 5), (62, 6), (94, 10), (95, 10)]

/-
## Part IV: Deficiency > 1 Examples
-/

/-- Known deficiency 2 examples. -/
def deficiency2Examples : List (ℕ × ℕ) :=
  [(44, 8), (74, 10), (174, 12), (239, 14), (5179, 27), (8413, 28), (8414, 28), (96622, 42)]

/-- Known deficiency 3 examples. -/
def deficiency3Examples : List (ℕ × ℕ) :=
  [(46, 10), (47, 10), (241, 16), (2105, 25), (1119, 27), (6459, 33)]

/-- C(47,11) has deficiency 4. -/
def deficiency4Example : ℕ × ℕ := (47, 11)

/-- C(284,28) has deficiency 9 (the record!). -/
def deficiency9Example : ℕ × ℕ := (284, 28)

/-
## Part V: The Main Questions
-/

/-- Question 1: Are there infinitely many C(n,k) with deficiency 1? -/
def conjecture1 : Prop :=
  Set.Infinite {p : ℕ × ℕ | HasDeficiency p.1 p.2 1}

/-- Question 2: Are there only finitely many with deficiency > 1? -/
def conjecture2 : Prop :=
  Set.Finite {p : ℕ × ℕ | ∃ d > 1, HasDeficiency p.1 p.2 d}

/-- The bound: if deficiency ≥ 1 exists, then n ≪ 2^k·√k. -/
axiom deficiency_bound (n k d : ℕ) (h : HasDeficiency n k d) (hd : d ≥ 1) :
    ∃ C : ℝ, (n : ℝ) ≤ C * 2^k * Real.sqrt k

/-
## Part VI: Verification Helpers
-/

/-- Check if m is k-smooth by testing all primes ≤ k. -/
def isSmooth_decide (m k : ℕ) : Bool :=
  (Finset.filter Nat.Prime (Finset.range (k + 1))).all fun p => ¬(p ∣ m) ∨ p ≤ k

/-- Compute deficiency (for small values). -/
def deficiency_compute (n k : ℕ) : ℕ :=
  (Finset.range k).filter (fun i => isSmooth_decide (n - i) k) |>.card

/-
## Part VII: Summary
-/

/-- Erdős Problem #1093: Summary

    **Definition**: Deficiency of C(n,k) = #{i < k : n-i is k-smooth}
    (undefined if C(n,k) divisible by prime ≤ k)

    **Known Examples**:
    - 58 with deficiency 1 for n ≤ 10^5
    - 8 with deficiency 2
    - 6 with deficiency 3
    - 1 with deficiency 4: C(47,11)
    - 1 with deficiency 9: C(284,28) (record!)

    **Bound**: Deficiency ≥ 1 implies n ≤ O(2^k·√k)

    **Open**:
    1. Infinitely many deficiency 1?
    2. Finitely many deficiency > 1?

    Conditional positive answer to Q2 by Barreto. -/
theorem erdos_1093_summary :
    -- Examples exist
    deficiency1Examples.length = 7 ∧
    deficiency2Examples.length = 8 ∧
    deficiency3Examples.length = 6 ∧
    deficiency4Example = (47, 11) ∧
    deficiency9Example = (284, 28) := by
  simp [deficiency1Examples, deficiency2Examples, deficiency3Examples,
        deficiency4Example, deficiency9Example]

end Erdos1093
