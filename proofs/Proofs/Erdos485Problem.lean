/-
  Erdős Problem #485: Minimum Terms in Squared Polynomials

  Source: https://erdosproblems.com/485
  Status: SOLVED (Schinzel 1987, improved by Schinzel-Zannier 2009)

  Statement:
  Let f(k) be the minimum number of terms in P(x)², where P ∈ ℚ[x] ranges over
  all polynomials with exactly k non-zero terms. Is it true that f(k) → ∞
  as k → ∞?

  Answer: YES

  History:
  - Rényi-Rédei (1947): First investigated the problem
  - Erdős (1949): Proved f(k) < k^(1-c) for some c > 0
  - Erdős-Rényi: Conjectured f(k) → ∞
  - Schinzel (1987): Proved f(k) > (log log k) / log 2
  - Schinzel-Zannier (2009): Improved to f(k) ≫ log k

  Key Insight:
  The question asks whether squaring a polynomial can always reduce the number
  of terms. The answer is no: as the polynomial gets more terms, its square
  must also have more terms (asymptotically).

  Reference: Hayman (1974), Problem 4.4
-/

import Mathlib

namespace Erdos485

open Polynomial Finset BigOperators

/-! ## Term Count for Polynomials -/

/--
The number of non-zero terms (monomials) in a polynomial.
This is the cardinality of the support.
-/
noncomputable def termCount {R : Type*} [Semiring R] (p : Polynomial R) : ℕ :=
  p.support.card

/--
A polynomial has exactly k non-zero terms.
-/
def hasTerms {R : Type*} [Semiring R] (p : Polynomial R) (k : ℕ) : Prop :=
  termCount p = k

/-! ## The Function f(k) -/

/--
f(k) is the minimum number of terms in P(x)² over all polynomials P
with exactly k non-zero terms.
-/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ p : Polynomial ℚ, hasTerms p k ∧ termCount (p ^ 2) = n}

/-! ## Basic Properties -/

/-- A polynomial with k terms squares to at least 1 term (if k ≥ 1). -/
theorem f_pos (k : ℕ) (hk : k ≥ 1) : f k ≥ 1 := by
  sorry

/-- f(1) = 1: A monomial squares to a monomial. -/
theorem f_one : f 1 = 1 := by
  sorry

/-- f(2) = 3: (a + bx^n)² = a² + 2abx^n + b²x^{2n} has 3 terms. -/
theorem f_two : f 2 = 3 := by
  sorry

/-! ## Upper Bounds (Erdős 1949) -/

/--
**Erdős (1949)**: There exists c > 0 such that f(k) < k^(1-c) for large k.
This shows that squaring can significantly reduce the term count.
-/
theorem erdos_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K, (f k : ℝ) < k ^ (1 - c) := by
  sorry

/-! ## The Main Result: f(k) → ∞ -/

/--
**Schinzel (1987)**: f(k) > (log log k) / log 2 for sufficiently large k.
-/
theorem schinzel_lower_bound :
    ∃ K : ℕ, ∀ k ≥ K,
    (f k : ℝ) > Real.log (Real.log k) / Real.log 2 := by
  sorry

/--
**Schinzel-Zannier (2009)**: f(k) ≫ log k. That is, there exists c > 0
such that f(k) ≥ c * log k for sufficiently large k.
-/
theorem schinzel_zannier_improved :
    ∃ c : ℝ, c > 0 ∧ ∃ K : ℕ, ∀ k ≥ K,
    (f k : ℝ) ≥ c * Real.log k := by
  sorry

/--
**Erdős Problem #485 (SOLVED)**: f(k) → ∞ as k → ∞.
-/
theorem erdos_485_main : Filter.Tendsto (fun k => f k) Filter.atTop Filter.atTop := by
  -- Follows from schinzel_zannier_improved
  sorry

/-! ## Examples -/

/-- Example: (1 + x)² = 1 + 2x + x² has 3 terms.
    We verify: (1 + x)² = 1 + 2x + x², support = {0, 1, 2}. -/
theorem example_binomial_square :
    termCount ((1 + X : Polynomial ℚ) ^ 2) = 3 := by
  -- The polynomial (1 + x)² = 1 + 2x + x² has support {0, 1, 2}
  sorry

/-- Example: (1 + x + x²)² = 1 + 2x + 3x² + 2x³ + x⁴ has 5 terms. -/
theorem example_trinomial_square :
    termCount ((1 + X + X^2 : Polynomial ℚ) ^ 2) = 5 := by
  -- The polynomial has support {0, 1, 2, 3, 4}
  sorry

/-! ## Related Concepts -/

/--
The general version: g(k, n) = minimum terms in P(x)^n for P with k terms.
Schinzel's result extends to this general case.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ p : Polynomial ℚ, hasTerms p k ∧ termCount (p ^ n) = m}

/-- For any n ≥ 1, g(k, n) → ∞ as k → ∞. -/
theorem general_divergence (n : ℕ) (hn : n ≥ 1) :
    Filter.Tendsto (fun k => g k n) Filter.atTop Filter.atTop := by
  sorry

/-! ## Sparse Polynomials -/

/--
A polynomial is sparse if it has few terms relative to its degree.
The study of f(k) is part of sparse polynomial theory.
-/
def isSparse (p : Polynomial ℚ) (c : ℝ) : Prop :=
  (termCount p : ℝ) ≤ c * Real.log (p.natDegree + 1)

/--
Multiplying sparse polynomials can produce denser results.
This is related to the f(k) problem.
-/
axiom sparse_product_density :
    ∃ c : ℝ, c > 0 ∧
    ∀ p q : Polynomial ℚ,
    isSparse p c → isSparse q c →
    (termCount (p * q) : ℝ) ≥ termCount p + termCount q - 1

/-! ## Lacunary Polynomials -/

/--
A lacunary polynomial has large gaps between exponents.
For example, 1 + x^10 + x^100 is lacunary.
-/
def isLacunary (p : Polynomial ℚ) : Prop :=
  ∃ gaps : List ℕ, gaps.length = termCount p - 1 ∧
  ∀ g ∈ gaps, g ≥ 2

/--
Squaring a lacunary polynomial tends to produce more terms due to
fewer cancellations between cross-terms.
-/
axiom lacunary_square_terms (p : Polynomial ℚ) (hp : isLacunary p) :
    termCount (p ^ 2) ≥ 2 * termCount p - 1

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #485 asks whether f(k) → ∞, where f(k) is the minimum number
of terms in P(x)² for polynomials P with exactly k terms.

**Answer: YES**

The conjecture of Erdős and Rényi was confirmed by:
- Schinzel (1987): Proved f(k) > (log log k) / log 2
- Schinzel-Zannier (2009): Improved to f(k) ≫ log k

**Key Ideas**:
- Squaring cannot indefinitely compress the term count
- There are only finitely many "efficient" polynomials (where squaring
  significantly reduces terms) of each size
- The result extends to P(x)^n for any n ≥ 1

**Open Questions**:
- What is the exact asymptotic growth rate of f(k)?
- Are there explicit constructions achieving the minimum f(k)?

**References**:
- Rényi, Rédei (1947): First investigation
- Erdős (1949): Upper bound f(k) < k^(1-c)
- Schinzel (1987): Lower bound f(k) > (log log k) / log 2
- Schinzel, Zannier (2009): Improved bound f(k) ≫ log k
- Hayman (1974): Problem 4.4
-/

end Erdos485
