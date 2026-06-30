/-
  Multiset-Coefficient (Rising Factorial) Identity

  Open Question (arithmetic-series-oq-02-oq-04-oq-01-oq-01):
  "Generalize to multiset coefficients: C(n+k-1, k) * k! = ∏ i in range k, (n + i)?"

  Answer: YES. The multiset coefficient ("n multichoose k") C(n+k-1, k) satisfies
    C(n+k-1, k) * k! = n*(n+1)*...*(n+k-1) = ascFactorial(n, k) = ∏ i in range k, (n+i).

  This is the rising-factorial analogue indexed so the product STARTS at n:
    - parent  OQ01 gives the descending form  C(n,   k) * k! = ∏ (n - i)
    - grandpa OQ04 gives the ascending  form  C(n+k, k) * k! = ascFactorial(n+1,k) = ∏ (n+1+i)
  Here the product starts at n itself, which is exactly the multiset coefficient
  C(n+k-1, k) = (number of size-k multisets drawn from n symbols).

  Combinatorial content: C(n+k-1, k) counts unordered k-multisets from n symbols
  ("stars and bars"); multiplying by k! recovers the rising factorial
  n*(n+1)*...*(n+k-1). This is the multiset dual of the parent's descending
  (falling) factorial C(n,k)*k! = n*(n-1)*...*(n-k+1).

  Proof: the identity is `Nat.ascFactorial_eq_factorial_mul_choose'`
    (n.ascFactorial k = k! * (n+k-1).choose k)
  composed with `Nat.ascFactorial_eq_prod_range`
    (n.ascFactorial k = ∏ i in range k, (n+i)).
  Both hold for all n (including the degenerate n = 0, where both sides vanish
  for k ≥ 1 and equal 1 for k = 0), so no case split or side condition is needed.

  Status: 0 axioms, 0 sorries, no native_decide.

  Parent: ArithmeticSeriesOQ02OQ04OQ01.lean (descending factorial)
  Grandparent: ArithmeticSeriesOQ02OQ04.lean (ascending factorial)
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Proofs.ArithmeticSeriesOQ02OQ04

namespace ArithmeticSeriesOQ02OQ04OQ01OQ01

open Finset BigOperators

-- ============================================================
-- Part I: The Main Identity
-- ============================================================

/-- **Multiset-Coefficient Identity**: C(n+k-1, k) * k! = ∏ i in range k, (n + i).

    The left side is "n multichoose k" times k!; the right side is the rising
    factorial n*(n+1)*...*(n+k-1). Reduces directly to two Mathlib lemmas:
    `Nat.ascFactorial_eq_factorial_mul_choose'` and
    `Nat.ascFactorial_eq_prod_range`. -/
theorem multichoose_factorial (n k : ℕ) :
    Nat.choose (n + k - 1) k * k.factorial = ∏ i ∈ range k, (n + i) := by
  rw [Nat.mul_comm, ← Nat.ascFactorial_eq_factorial_mul_choose',
      Nat.ascFactorial_eq_prod_range]

/-- **Rising Factorial Closed Form**: C(n+k-1, k) * k! = ascFactorial(n, k).
    The same identity, packaged against Mathlib's `Nat.ascFactorial`. -/
theorem multichoose_eq_ascFactorial (n k : ℕ) :
    Nat.choose (n + k - 1) k * k.factorial = n.ascFactorial k := by
  rw [Nat.mul_comm, ← Nat.ascFactorial_eq_factorial_mul_choose']

-- ============================================================
-- Part II: Structural Properties
-- ============================================================

/-- **k! divides the rising product**: equivalently, the multiset coefficient
    C(n+k-1, k) = (∏ i in range k, (n+i)) / k! is an integer. -/
theorem factorial_dvd_rising_product (n k : ℕ) :
    k.factorial ∣ ∏ i ∈ range k, (n + i) :=
  ⟨Nat.choose (n + k - 1) k, by rw [← multichoose_factorial]; exact Nat.mul_comm _ _⟩

/-- **Multiset vs. ascending duality**: the multiset form starts its product at n,
    while the grandparent's ascending (simplicial) form starts at n+1.

    - multiset    : C(n+k-1, k) * k! = ∏ i in range k, (n + i)     = n(n+1)···(n+k-1)
    - ascending   : C(n+k,   k) * k! = ∏ i in range k, (n + 1 + i) = (n+1)(n+2)···(n+k)

    They are the same ordered-selection count read off two adjacent index origins. -/
theorem multiset_ascending_duality (n k : ℕ) :
    Nat.choose (n + k - 1) k * k.factorial = ∏ i ∈ range k, (n + i) ∧
    ArithmeticSeriesOQ02.simplicial k n * k.factorial = ∏ i ∈ range k, (n + 1 + i) :=
  ⟨multichoose_factorial n k, ArithmeticSeriesOQ02OQ04.simplicial_product k n⟩

-- ============================================================
-- Part III: Low-Dimensional Specializations
-- ============================================================

/-- k = 1: C(n, 1) * 1! = n. -/
theorem multichoose_factorial_one (n : ℕ) :
    Nat.choose (n + 1 - 1) 1 * Nat.factorial 1 = n := by
  rw [multichoose_factorial, Finset.prod_range_one, Nat.add_zero]

/-- k = 2: C(n+1, 2) * 2! = n*(n+1). -/
theorem multichoose_factorial_two (n : ℕ) :
    Nat.choose (n + 2 - 1) 2 * Nat.factorial 2 = n * (n + 1) := by
  rw [multichoose_factorial, Finset.prod_range_succ, Finset.prod_range_one]; ring

/-- k = 3: C(n+2, 3) * 3! = n*(n+1)*(n+2). -/
theorem multichoose_factorial_three (n : ℕ) :
    Nat.choose (n + 3 - 1) 3 * Nat.factorial 3 = n * (n + 1) * (n + 2) := by
  rw [multichoose_factorial, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_one]; ring

/-- n = 1: C(1+k-1, k) * k! = C(k, k) * k! = k!. The product 1·2···k is just k!. -/
theorem multichoose_factorial_n_one (k : ℕ) :
    Nat.choose (1 + k - 1) k * k.factorial = k.factorial := by
  rw [show 1 + k - 1 = k from by omega, Nat.choose_self, Nat.one_mul]

-- ============================================================
-- Part IV: Concrete Verification (decide — no native_decide)
-- ============================================================

/-- C(4,3) * 3! = 2*3*4 = 24. C(4,3) = 4, 4 * 6 = 24. -/
theorem check_n2_k3 : Nat.choose (2 + 3 - 1) 3 * Nat.factorial 3 = 24 := by decide

/-- C(4,2) * 2! = 3*4 = 12. C(4,2) = 6, 6 * 2 = 12. -/
theorem check_n3_k2 : Nat.choose (3 + 2 - 1) 2 * Nat.factorial 2 = 12 := by decide

/-- The product side agrees: ∏ i in range 3, (2 + i) = 2*3*4 = 24. -/
theorem check_product_n2_k3 : ∏ i ∈ range 3, (2 + i) = 24 := by
  rw [← multichoose_factorial]; decide

/-
  Summary

  This file proves the multiset-coefficient generalization of the
  descending/ascending factorial identities, 0 axioms / 0 sorries / no
  native_decide:

    Part I  - multichoose_factorial:        C(n+k-1, k) * k! = ∏ i in range k, (n + i)
              multichoose_eq_ascFactorial:   C(n+k-1, k) * k! = ascFactorial(n, k)
    Part II - factorial_dvd_rising_product:  k! ∣ ∏ i in range k, (n + i)
              multiset_ascending_duality:    multiset (start n) vs ascending (start n+1)
    Part III- multichoose_factorial_one:     C(n,   1) * 1 = n
              multichoose_factorial_two:     C(n+1, 2) * 2 = n*(n+1)
              multichoose_factorial_three:   C(n+2, 3) * 6 = n*(n+1)*(n+2)
              multichoose_factorial_n_one:   C(k,   k) * k! = k!
    Part IV - concrete decide checks

  Key insight:
    descending : C(n,    k) * k! = n*(n-1)*...*(n-k+1)   [OQ01]
    ascending  : C(n+k,  k) * k! = (n+1)*(n+2)*...*(n+k) [OQ04]
    multiset   : C(n+k-1,k) * k! = n*(n+1)*...*(n+k-1)   [this file]
    The three are the same ordered-selection count read off three index origins;
    the multiset form starts the product at n, matching n-multichoose-k.
-/

end ArithmeticSeriesOQ02OQ04OQ01OQ01
