/-
  Erdős Problem #257: Irrationality of Sums over 1/(2^n - 1)

  **Problem**: Let A ⊆ ℕ be an infinite set. Is
    ∑_{n ∈ A} 1/(2^n - 1)
  always irrational?

  **Status**: PARTIALLY SOLVED
  - For A = ℕ: YES, proved by Erdős (1948)
  - For A = primes: YES, proved by Tao & Teräväinen (2025)
  - For general infinite A: OPEN

  **Key Identity**: When A = ℕ, we have
    ∑_n 1/(2^n - 1) = ∑_n d(n)/2^n
  where d(n) is the divisor function.

  Reference: https://erdosproblems.com/257
  Citation: Erdős, P. "On arithmetical properties of Lambert series."
            J. Indian Math. Soc. (N.S.) (1948), 63-66.
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Order.Floor.Div

namespace Erdos257

open Set BigOperators Nat

/-! ## Definitions -/

/-- The sum ∑_{n ∈ A} 1/(2^n - 1) for a set A ⊆ ℕ.
    Each term 1/(2^n - 1) appears in Lambert series and has deep
    connections to number-theoretic functions. -/
noncomputable def lambertSum (A : Set ℕ) : ℝ :=
  ∑' n : A, (1 : ℝ) / (2 ^ (n : ℕ) - 1)

/-- The divisor-weighted sum ∑_n d(n)/2^n where d(n) = |divisors of n|.
    This equals the Lambert sum when taken over all positive integers. -/
noncomputable def divisorSum : ℝ :=
  ∑' n : ℕ, (n.divisors.card : ℝ) / (2 ^ n)

/-! ## The Key Identity -/

/--
**Lambert Series Identity** (undergraduate level):

The sum ∑_{n≥1} 1/(2^n - 1) equals ∑_{n≥1} d(n)/2^n.

This follows from expanding 1/(2^n - 1) = ∑_{k≥1} 1/2^{kn} and rearranging:
  ∑_n 1/(2^n - 1) = ∑_n ∑_{k≥1} 1/2^{kn}
                  = ∑_m (number of divisors of m)/2^m
                  = ∑_m d(m)/2^m

The rearrangement is justified because all terms are positive.
-/
axiom lambert_series_identity :
    lambertSum (univ : Set ℕ) = divisorSum

/-! ## Erdős's 1948 Result -/

/--
**Erdős (1948)**: The sum ∑_n d(n)/2^n is irrational.

Erdős proved this using properties of Lambert series and the
arithmetic of the divisor function. The key insight is that
d(n)/2^n cannot have a "too regular" pattern that would
allow cancellation to a rational value.
-/
axiom erdos_divisor_sum_irrational : Irrational divisorSum

/--
**Corollary**: The full Lambert sum ∑_{n≥1} 1/(2^n - 1) is irrational.

This follows immediately from the identity and Erdős's result.
-/
theorem full_lambert_sum_irrational :
    Irrational (lambertSum (univ : Set ℕ)) := by
  rw [lambert_series_identity]
  exact erdos_divisor_sum_irrational

/-! ## The Open Problem -/

/--
**Erdős Problem #257** (Open):

Is ∑_{n ∈ A} 1/(2^n - 1) irrational for EVERY infinite set A ⊆ ℕ?

The answer is YES for:
- A = ℕ (Erdős 1948)
- A = primes (Tao-Teräväinen 2025)
- A = prime powers (Tao-Teräväinen 2025)
- A with pairwise coprime elements and ∑_{n∈A} 1/n < ∞ (Erdős 1968)

The general case remains open. We state this as a conjecture.
-/
axiom erdos_257_conjecture :
    ∀ A : Set ℕ, A.Infinite → Irrational (lambertSum A)

/-! ## Concrete Examples -/

/-- The first few terms of the divisor function:
    d(1) = 1, d(2) = 2, d(3) = 2, d(4) = 3, d(5) = 2, d(6) = 4 -/
example : (1 : ℕ).divisors.card = 1 := by native_decide
example : (2 : ℕ).divisors.card = 2 := by native_decide
example : (3 : ℕ).divisors.card = 2 := by native_decide
example : (4 : ℕ).divisors.card = 3 := by native_decide
example : (5 : ℕ).divisors.card = 2 := by native_decide
example : (6 : ℕ).divisors.card = 4 := by native_decide

/-- Perfect numbers have d(n) = 2 + sum of proper divisors / n... but
    more simply, 28 = 1+2+4+7+14 has exactly 6 divisors. -/
example : (28 : ℕ).divisors.card = 6 := by native_decide

/-- The denominators 2^n - 1 are Mersenne numbers.
    When n is prime, 2^n - 1 might be a Mersenne prime. -/
example : 2^2 - 1 = 3 := by native_decide
example : 2^3 - 1 = 7 := by native_decide
example : 2^5 - 1 = 31 := by native_decide
example : 2^7 - 1 = 127 := by native_decide

end Erdos257
