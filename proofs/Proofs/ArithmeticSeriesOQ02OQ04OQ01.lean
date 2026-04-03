/-
  Descending Factorial Analogue of Arithmetic Series

  Open Question (arithmetic-series-oq-02-oq-04-oq-01):
  "Formalize descending factorial analogue of arithmetic series."

  Answer: The key identity is C(n, k) * k! = descFactorial(n, k) = n*(n-1)*...*(n-k+1).

  This is the descending (falling) factorial counterpart to:
    C(n+k, k) * k! = ascFactorial(n+1, k) = (n+1)*(n+2)*...*(n+k)   [ArithmeticSeriesOQ02OQ04]

  The descending factorial counts ordered k-selections from {1,...,n}:
    C(n,k) = unordered selections
    C(n,k) * k! = ordered selections = n*(n-1)*...*(n-k+1)

  Mathlib reference: Nat.descFactorial_eq_factorial_mul_choose
  Status: 0 axioms, 0 sorries

  Parent: ArithmeticSeriesOQ02OQ04.lean (ascending factorial analogue)
-/

import Proofs.ArithmeticSeriesOQ02OQ04
import Mathlib.Data.Nat.Factorial.BigOperators

namespace ArithmeticSeriesOQ02OQ04OQ01

open Finset BigOperators ArithmeticSeriesOQ02 ArithmeticSeriesOQ02OQ04

-- ============================================================
-- Part I: The Main Identity
-- ============================================================

/-- **Descending Factorial Identity**: C(n, k) * k! = descFactorial(n, k).

    This is the ordered selection formula:
    - C(n, k) = unordered k-selections from n objects
    - k! = ways to order k objects
    - C(n, k) * k! = ordered k-selections = n*(n-1)*...*(n-k+1)

    Direct from Mathlib's `Nat.descFactorial_eq_factorial_mul_choose`. -/
theorem choose_descFactorial (n k : ℕ) :
    Nat.choose n k * k.factorial = n.descFactorial k := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  ring

-- ============================================================
-- Part II: Explicit Product Formula
-- ============================================================

/-- **Explicit Product Formula**: C(n, k) * k! = ∏ i in range k, (n - i).

    Unfolding descFactorial: n*(n-1)*...*(n-k+1). -/
theorem choose_product (n k : ℕ) :
    Nat.choose n k * k.factorial = ∏ i ∈ range k, (n - i) := by
  rw [choose_descFactorial, Nat.descFactorial_eq_prod_range]

-- ============================================================
-- Part III: Structural Properties
-- ============================================================

/-- **Full Factorial Identity**: C(n, k) * k! * (n-k)! = n!

    Equivalently: the descending factorial times (n-k)! = n! -/
theorem choose_full_factorial (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k * k.factorial * (n - k).factorial = n.factorial := by
  rw [choose_descFactorial]
  exact Nat.factorial_mul_descFactorial h

/-- **Factorial divides descending factorial**: k! divides descFactorial(n, k).
    This is equivalent to: C(n,k) is a natural number. -/
theorem factorial_dvd_descFactorial (n k : ℕ) :
    k.factorial ∣ n.descFactorial k :=
  ⟨Nat.choose n k, (choose_descFactorial n k).symm⟩

/-- **descFactorial self is factorial**: n.descFactorial n = n! -/
theorem descFactorial_self_eq_factorial (n : ℕ) :
    n.descFactorial n = n.factorial :=
  Nat.descFactorial_self n

-- ============================================================
-- Part IV: Ascending vs Descending — Duality
-- ============================================================

/-- **Duality**: C(n, k) * k! = descFactorial(n, k) and
    C(n+k, k) * k! = ascFactorial(n+1, k).

    These are dual: ascending uses offset n+1, descending uses n directly.
    Together they cover the two standard ways to count ordered k-selections. -/
theorem ascending_descending_duality (k n : ℕ) :
    Nat.choose (n + k) k * k.factorial = Nat.ascFactorial (n + 1) k ∧
    Nat.choose (n + k) k * k.factorial = (n + k).descFactorial k := by
  constructor
  · -- This is simplicial_factorial from ArithmeticSeriesOQ02OQ04
    exact simplicial_factorial k n
  · -- Descending form
    exact choose_descFactorial (n + k) k

-- ============================================================
-- Part V: Low-Dimensional Specializations
-- ============================================================

/-- k=1: C(n,1) * 1! = n. -/
theorem choose_descFactorial_one (n : ℕ) :
    Nat.choose n 1 * 1.factorial = n := by
  rw [choose_descFactorial, Nat.descFactorial_one]

/-- k=2: C(n,2) * 2! = n*(n-1). -/
theorem choose_descFactorial_two (n : ℕ) :
    Nat.choose n 2 * 2.factorial = n * (n - 1) := by
  rw [choose_descFactorial]
  simp [Nat.descFactorial, Nat.descFactorial_succ, Nat.descFactorial_one]
  ring

/-- k=3: C(n,3) * 3! = n*(n-1)*(n-2). -/
theorem choose_descFactorial_three (n : ℕ) :
    Nat.choose n 3 * 3.factorial = n * (n - 1) * (n - 2) := by
  rw [choose_descFactorial]
  simp [Nat.descFactorial, Nat.descFactorial_succ, Nat.descFactorial_one]
  ring

-- ============================================================
-- Part VI: Concrete Verification
-- ============================================================

/-- C(5,2) * 2! = 5*4 = 20. C(5,2) = 10, 10 * 2 = 20. -/
theorem check_n5_k2 : Nat.choose 5 2 * 2.factorial = 20 := by native_decide

/-- C(6,3) * 3! = 6*5*4 = 120. C(6,3) = 20, 20 * 6 = 120. -/
theorem check_n6_k3 : Nat.choose 6 3 * 3.factorial = 120 := by native_decide

/-- Product formula agrees: ∏ i in range 2, (5 - i) = 5*4 = 20. -/
theorem check_product_n5_k2 : ∏ i ∈ range 2, (5 - i) = 20 := by native_decide

/-
  Summary

  This file proves 11 theorems with 0 sorries and 0 axioms:

  Part I - Main Identity:
    choose_descFactorial: C(n,k) * k! = descFactorial(n, k)

  Part II - Explicit Product:
    choose_product: C(n,k) * k! = ∏ i in range k, (n - i)

  Part III - Structural Properties:
    choose_full_factorial: C(n,k) * k! * (n-k)! = n!
    factorial_dvd_descFactorial: k! | descFactorial(n, k)
    descFactorial_self_eq_factorial: descFactorial(n, n) = n!

  Part IV - Duality:
    ascending_descending_duality: connects ascending and descending forms

  Part V - Specializations:
    choose_descFactorial_one:   C(n,1) * 1  = n
    choose_descFactorial_two:   C(n,2) * 2  = n*(n-1)
    choose_descFactorial_three: C(n,3) * 6  = n*(n-1)*(n-2)

  Part VI - Concrete Checks:
    check_n5_k2: C(5,2) * 2! = 20
    check_n6_k3: C(6,3) * 6! = 120
    check_product_n5_k2: ∏ i in range 2, (5-i) = 20

  Key Insight:
    Descending: C(n,k) * k! = n*(n-1)*...*(n-k+1)   [ordered selections from n]
    Ascending:  C(n+k,k) * k! = (n+1)*(n+2)*...*(n+k) [ordered selections offset by n]
    These are dual formulas counting the same combinatorial objects from different angles.
-/

end ArithmeticSeriesOQ02OQ04OQ01
