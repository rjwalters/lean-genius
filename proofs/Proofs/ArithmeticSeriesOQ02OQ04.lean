/-
  Rising Factorial and the Simplicial Number Identity

  Open Question (arithmetic-series-oq-02-oq-04):
  "Formalize the general closed form S_k(n) * k! = (n+1)(n+2)...(n+k) for all k,
   and prove it equals Nat.choose (n+k) k * k! by the binomial coefficient formula."

  Answer: YES. The simplicial number S_k(n) = C(n+k, k) satisfies
    S_k(n) * k! = (n+1)(n+2)...(n+k) = ascFactorial(n+1, k)

  This is the ascending factorial (Pochhammer symbol). The identity connects
  binomial coefficients to ordered selections: C(n+k, k) counts unordered
  k-subsets from {1,...,n+k}, and multiplying by k! gives the number of
  ordered selections -- the product (n+1)(n+2)...(n+k).

  Status (0 axioms, 0 sorries)

  Parent: ArithmeticSeriesOQ02.lean (0 axioms, 0 sorries)
  References:
  - Graham, Knuth, Patashnik (1994): "Concrete Mathematics", S5.1
  - Mathlib: Nat.ascFactorial_eq_factorial_mul_choose
-/

import Proofs.ArithmeticSeriesOQ02

namespace ArithmeticSeriesOQ02OQ04

open Finset BigOperators ArithmeticSeriesOQ02

-- ============================================================
-- Part I: The Main Identity
-- ============================================================

/-- **Rising Factorial Identity**: The k-th simplicial number times k! equals
    the ascending factorial (n+1)(n+2)...(n+k).

    C(n+k, k) * k! = ascFactorial(n+1, k)

    Direct from Mathlib's `ascFactorial_eq_factorial_mul_choose`. -/
theorem simplicial_factorial (k n : ℕ) :
    simplicial k n * k.factorial = Nat.ascFactorial (n + 1) k := by
  unfold simplicial
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  exact mul_comm _ _

-- ============================================================
-- Part II: Explicit Product Formula
-- ============================================================

/-- The ascending factorial as an explicit product:
    ascFactorial(n, k) = n * (n+1) * ... * (n+k-1) = prod i in range k, (n + i). -/
theorem ascFactorial_eq_prod (n k : ℕ) :
    Nat.ascFactorial n k = ∏ i ∈ range k, (n + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← ih]
    exact mul_comm (n + k) (Nat.ascFactorial n k)

/-- **Explicit Product Formula**: S_k(n) * k! = prod i in range k, (n + 1 + i).
    This makes explicit that the identity is (n+1)(n+2)...(n+k). -/
theorem simplicial_product (k n : ℕ) :
    simplicial k n * k.factorial = ∏ i ∈ range k, (n + 1 + i) := by
  rw [simplicial_factorial, ascFactorial_eq_prod]

-- ============================================================
-- Part III: Full Factorial Identity
-- ============================================================

/-- **Full Factorial Expansion**: S_k(n) * k! * n! = (n+k)!

    The complete factorial form: C(n+k, k) * k! * n! = (n+k)!
    Immediate from `Nat.choose_mul_factorial_mul_factorial`. -/
theorem simplicial_full_factorial (k n : ℕ) :
    simplicial k n * k.factorial * n.factorial = (n + k).factorial := by
  simp only [simplicial]
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k by omega)
  rwa [show n + k - k = n from by omega] at h

/-- **Factorial divides ascending factorial**: k! divides ascFactorial(n+1, k).
    This is the combinatorial content: C(n+k,k) = ascFactorial(n+1,k) / k!
    is always a natural number. -/
theorem factorial_dvd_ascFactorial (n k : ℕ) :
    k.factorial ∣ Nat.ascFactorial (n + 1) k :=
  ⟨simplicial k n, by rw [Nat.mul_comm, simplicial_factorial]⟩

-- ============================================================
-- Part IV: Low-Dimensional Specializations
-- ============================================================

/-- k=1: S_1(n) * 1! = n + 1. -/
theorem simplicial_factorial_one (n : ℕ) :
    simplicial 1 n * Nat.factorial 1 = n + 1 := by
  rw [simplicial_product, Finset.prod_range_one]

/-- k=2: S_2(n) * 2! = (n+1)(n+2). Matches `simplicial_two_formula`. -/
theorem simplicial_factorial_two (n : ℕ) :
    simplicial 2 n * Nat.factorial 2 = (n + 1) * (n + 2) := by
  rw [simplicial_product]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.add_zero]

/-- k=3: S_3(n) * 3! = (n+1)(n+2)(n+3). Matches `simplicial_three_formula`. -/
theorem simplicial_factorial_three (n : ℕ) :
    simplicial 3 n * Nat.factorial 3 = (n + 1) * (n + 2) * (n + 3) := by
  rw [simplicial_product]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.add_zero]

-- ============================================================
-- Part V: Concrete Verification
-- ============================================================

/-- S_4(3) * 4! = 4*5*6*7 = 840. C(7,4) = 35, 35 * 24 = 840. -/
theorem check_k4_n3 : simplicial 4 3 * Nat.factorial 4 = 840 := by decide

/-- S_5(2) * 5! = 3*4*5*6*7 = 2520. C(7,5) = 21, 21 * 120 = 2520. -/
theorem check_k5_n2 : simplicial 5 2 * Nat.factorial 5 = 2520 := by decide

/-- The product formula agrees: prod i in range 4, (4 + i) = 4*5*6*7 = 840. -/
theorem check_product : ∏ i ∈ range 4, (3 + 1 + i) = 840 := by decide

/-
  Summary

  This file proves 11 theorems with 0 sorries and 0 axioms:

  Part I - Main Identity:
    simplicial_factorial: S_k(n) * k! = ascFactorial(n+1, k)

  Part II - Explicit Product:
    ascFactorial_eq_prod: ascFactorial(n, k) = prod i in range k, (n + i)
    simplicial_product: S_k(n) * k! = prod i in range k, (n + 1 + i)

  Part III - Structural Properties:
    simplicial_full_factorial: S_k(n) * k! * n! = (n+k)!
    factorial_dvd_ascFactorial: k! | ascFactorial(n+1, k)

  Part IV - Specializations:
    simplicial_factorial_one:   S_1(n) * 1  = n + 1
    simplicial_factorial_two:   S_2(n) * 2  = (n+1)(n+2)
    simplicial_factorial_three: S_3(n) * 6  = (n+1)(n+2)(n+3)

  Part V - Concrete Checks:
    check_k4_n3: S_4(3) * 24 = 840
    check_k5_n2: S_5(2) * 120 = 2520
    check_product: prod i in [0..4), (4+i) = 840

  Key Insight:
    The identity S_k(n) * k! = (n+1)(n+2)...(n+k) reveals that simplicial
    numbers (binomial coefficients) are "compressed" rising factorials. The
    binomial coefficient C(n+k,k) counts unordered selections; multiplying
    by k! (the number of orderings) recovers the ordered count -- the product
    of consecutive integers. This is the combinatorial reason why C(n+k,k)
    is always an integer despite being defined as a ratio of factorials.
-/

end ArithmeticSeriesOQ02OQ04
