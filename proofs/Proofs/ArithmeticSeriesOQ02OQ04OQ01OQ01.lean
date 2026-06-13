/-
  Multiset-Coefficient (Rising Factorial) Identity

  Open Question (arithmetic-series-oq-02-oq-04-oq-01-oq-01):
  "Generalize to multiset coefficients: C(n+k-1, k) * k! = ∏ i in range k, (n + i)?"

  Answer: YES. The multiset coefficient ("n multichoose k") C(n+k-1, k) satisfies
    C(n+k-1, k) * k! = n*(n+1)*...*(n+k-1) = ascFactorial(n, k) = ∏ i in range k, (n+i).

  This is the rising-factorial analogue indexed so the product STARTS at n:
    - parent  OQ01 gives the descending form  C(n,k)   * k! = ∏ (n - i)
    - grandpa OQ04 gives the ascending  form  C(n+k,k) * k! = ascFactorial(n+1,k) = ∏ (n+1+i)
  Here the product starts at n itself, which is exactly the multiset coefficient
  C(n+k-1, k) = (number of size-k multisets drawn from n symbols).

  Combinatorial content: C(n+k-1, k) counts unordered k-multisets from n symbols;
  multiplying by k! recovers the rising factorial n*(n+1)*...*(n+k-1). This is the
  multiset / "stars and bars" dual of the parent's descending (falling) factorial.

  Proof strategy (reduces entirely to build-checked lemmas):
    - n = 0 is degenerate: for k ≥ 1 both sides vanish (C(k-1,k) = 0 and the
      product contains the i = 0 factor 0); k = 0 gives 1 = 1.
    - n = m+1 is the grandparent's identity shifted by one:
        C(m+k, k) * k! = ascFactorial(m+1, k) = ∏ i in range k, (m+1+i)
      via `Nat.ascFactorial_eq_factorial_mul_choose` (Mathlib) and
      `ArithmeticSeriesOQ02OQ04.ascFactorial_eq_prod`.

  STATUS: DRAFT — proof written but NOT build-verified (Docker/lake outage
  2026-06-13; see project memory "Verification blackout 2026-06-13"). It is
  intentionally NOT yet registered in proofs/Proofs.lean so it cannot affect the
  whole-library build. To verify: add `import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ01`
  to Proofs.lean and run
    ./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ01

  Parent: ArithmeticSeriesOQ02OQ04OQ01.lean (descending factorial)
-/

import Proofs.ArithmeticSeriesOQ02OQ04OQ01

namespace ArithmeticSeriesOQ02OQ04OQ01OQ01

open Finset BigOperators

-- ============================================================
-- Part I: The Main Identity
-- ============================================================

/-- **Multiset-Coefficient Identity**: C(n+k-1, k) * k! = ∏ i in range k, (n + i).

    The left side is "n multichoose k" times k!; the right side is the rising
    factorial n*(n+1)*...*(n+k-1). For n ≥ 1 this is the grandparent's
    `simplicial_factorial` shifted by one; the n = 0 case is degenerate (both
    sides vanish for k ≥ 1, and equal 1 for k = 0). -/
theorem multichoose_factorial (n k : ℕ) :
    Nat.choose (n + k - 1) k * k.factorial = ∏ i ∈ range k, (n + i) := by
  rcases n with _ | m
  · -- n = 0
    rcases k with _ | j
    · simp
    · -- k = j + 1 ≥ 1: both sides are 0
      rw [show 0 + (j + 1) - 1 = j from by omega,
          Nat.choose_eq_zero_of_lt (Nat.lt_succ_self j), Nat.zero_mul]
      symm
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos j))
      simp
  · -- n = m + 1: reduce to the ascending factorial identity from OQ04
    rw [← ArithmeticSeriesOQ02OQ04.ascFactorial_eq_prod,
        show m + 1 + k - 1 = m + k from by omega,
        Nat.ascFactorial_eq_factorial_mul_choose]
    ring

-- ============================================================
-- Part II: Low-Dimensional Specializations
-- ============================================================

/-- k = 1: C(n, 1) * 1! = n. -/
theorem multichoose_factorial_one (n : ℕ) :
    Nat.choose (n + 1 - 1) 1 * 1.factorial = n := by
  rw [multichoose_factorial, Finset.prod_range_one, Nat.add_zero]

/-- k = 2: C(n+1, 2) * 2! = n*(n+1). -/
theorem multichoose_factorial_two (n : ℕ) :
    Nat.choose (n + 2 - 1) 2 * 2.factorial = n * (n + 1) := by
  rw [multichoose_factorial, Finset.prod_range_succ, Finset.prod_range_one]; ring

/-- k = 3: C(n+2, 3) * 3! = n*(n+1)*(n+2). -/
theorem multichoose_factorial_three (n : ℕ) :
    Nat.choose (n + 3 - 1) 3 * 3.factorial = n * (n + 1) * (n + 2) := by
  rw [multichoose_factorial, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_one]; ring

-- ============================================================
-- Part III: Concrete Verification
-- ============================================================

/-- C(4,3) * 3! = 2*3*4 = 24. C(4,3) = 4, 4 * 6 = 24. -/
theorem check_n2_k3 : Nat.choose (2 + 3 - 1) 3 * 3.factorial = 24 := by native_decide

/-- C(4,2) * 2! = 3*4 = 12. C(4,2) = 6, 6 * 2 = 12. -/
theorem check_n3_k2 : Nat.choose (3 + 2 - 1) 2 * 2.factorial = 12 := by native_decide

/-- The product agrees: ∏ i in range 3, (2 + i) = 2*3*4 = 24. -/
theorem check_product_n2_k3 : ∏ i ∈ range 3, (2 + i) = 24 := by native_decide

/-
  Summary

  This file (DRAFT, awaiting Docker build verification) states the multiset-
  coefficient generalization of the descending/ascending factorial identities:

    Part I  - multichoose_factorial:        C(n+k-1, k) * k! = ∏ i in range k, (n + i)
    Part II - multichoose_factorial_one:    C(n,   1) * 1 = n
              multichoose_factorial_two:    C(n+1, 2) * 2 = n*(n+1)
              multichoose_factorial_three:  C(n+2, 3) * 6 = n*(n+1)*(n+2)
    Part III- concrete native_decide checks

  Key insight:
    descending : C(n,    k) * k! = n*(n-1)*...*(n-k+1)   [OQ01]
    ascending  : C(n+k,  k) * k! = (n+1)*(n+2)*...*(n+k) [OQ04]
    multiset   : C(n+k-1,k) * k! = n*(n+1)*...*(n+k-1)   [this file]
    The three are the same ordered-selection count read off three index origins;
    the multiset form starts the product at n, matching n-multichoose-k.
-/

end ArithmeticSeriesOQ02OQ04OQ01OQ01
