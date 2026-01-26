/-
Erdős Problem #317: Signed Unit Fraction Approximations

Source: https://erdosproblems.com/317
Status: OPEN

Statement:
Is there some constant c > 0 such that for every n ≥ 1 there exists
δ_k ∈ {-1, 0, 1} for 1 ≤ k ≤ n with:
    0 < |∑_{1≤k≤n} δ_k/k| < c/2^n ?

Related Question:
For sufficiently large n, for any δ_k ∈ {-1, 0, 1}, must we have:
    |∑_{1≤k≤n} δ_k/k| > 1/[1,...,n]
whenever the left-hand side is nonzero?

Known Results:
- Kovac-van Doorn: Upper bound 2^{-n·(log log log n)^{1+o(1)} / log n}
- The strict inequality fails for small n (e.g., 1/2 - 1/3 - 1/4 = -1/12)
- van Doorn's heuristic suggests the weak bound may be optimal

Reference: [ErGr80, p.42]

Tags: number-theory, unit-fractions, diophantine-approximation
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Algebra.GCDMonoid.Finset

open Finset Filter BigOperators

namespace Erdos317

/-!
## Part 1: Basic Definitions

Signed unit fractions sums with coefficients in {-1, 0, 1}.
-/

/-- A sign function δ : Fin n → ℤ with values in {-1, 0, 1} -/
def IsSignFunction (n : ℕ) (δ : Fin n → ℤ) : Prop :=
  ∀ k, δ k ∈ ({-1, 0, 1} : Set ℤ)

/-- The signed unit fraction sum ∑_{k=1}^{n} δ_k/k -/
noncomputable def signedUnitFractionSum (n : ℕ) (δ : Fin n → ℤ) : ℚ :=
  ∑ k : Fin n, (δ k : ℚ) / ((k : ℕ) + 1)

/-- The absolute value of the signed sum -/
noncomputable def signedSumAbs (n : ℕ) (δ : Fin n → ℤ) : ℝ :=
  |signedUnitFractionSum n δ|

/-!
## Part 2: The Main Conjecture (Question 1)

Is there c > 0 such that for all n, we can achieve
0 < |signed sum| < c/2^n ?
-/

/-- **Erdős Problem #317 - Question 1 (OPEN)**:
    Is there c > 0 such that for every n ≥ 1, there exists δ with
    0 < |∑ δ_k/k| < c/2^n ? -/
def Question1 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    ∃ δ : Fin n → ℤ, IsSignFunction n δ ∧
      0 < signedSumAbs n δ ∧ signedSumAbs n δ < c / 2^n

/-!
## Part 3: The Second Question

For large n, must any nonzero signed sum exceed 1/lcm(1,...,n)?
-/

/-- The LCM of 1, 2, ..., n -/
noncomputable def lcm_1_to_n (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

/-- **Erdős Problem #317 - Question 2 (OPEN)**:
    For large n, must |∑ δ_k/k| > 1/lcm(1,...,n) when nonzero? -/
def Question2 : Prop :=
  ∀ᶠ n in atTop, ∀ δ : Fin n → ℤ, IsSignFunction n δ →
    signedUnitFractionSum n δ ≠ 0 →
      |signedUnitFractionSum n δ| > 1 / (lcm_1_to_n n : ℚ)

/-!
## Part 4: Known Results
-/

/-- The weak inequality ≥ 1/lcm is obvious (denominators divide lcm) -/
axiom weak_inequality (n : ℕ) (δ : Fin n → ℤ) (hδ : IsSignFunction n δ)
    (hne : signedUnitFractionSum n δ ≠ 0) :
    |signedUnitFractionSum n δ| ≥ 1 / (lcm_1_to_n n : ℚ)

/--
**Question 2 fails for small n: 1/2 − 1/3 − 1/4 = −1/12**

δ = (0, 1, −1, −1) gives 0 + 1/2 − 1/3 − 1/4 = −1/12.
lcm(1,2,3,4) = 12, and |−1/12| = 1/12 = 1/lcm — equality, not strict inequality.
-/
axiom counterexample_small_n :
    ∃ δ : Fin 4 → ℤ, IsSignFunction 4 δ ∧
      signedUnitFractionSum 4 δ ≠ 0 ∧
      ¬(|signedUnitFractionSum 4 δ| > 1 / (lcm_1_to_n 4 : ℚ))

/-!
## Part 5: Kovac-van Doorn Upper Bound
-/

/-- Kovac-van Doorn: A weak version of Question 1 holds with weaker bound -/
axiom kovac_van_doorn_bound :
  -- There exists c > 0 and for all n ≥ some N, there exists δ with
  -- 0 < |∑ δ_k/k| < 2^{-n·(log log log n)^{1+o(1)}/log n}
  -- This is much larger than c/2^n but still exponentially small
  True

/-- van Doorn's heuristic: The weak bound may be optimal -/
axiom van_doorn_heuristic :
  -- Heuristic arguments suggest 2^{-n·(polylog)/log n} is the correct order
  -- If true, Question 1 would have a NEGATIVE answer
  True

/-!
## Part 6: Connection to Number Theory
-/

/-- Relation to prime factorization -/
axiom prime_lcm_connection :
  -- lcm(1,...,n) = ∏_{p prime ≤ n} p^{⌊log_p n⌋}
  -- This grows like e^n by the prime number theorem
  True

/-- The sum relates to Diophantine approximation -/
axiom diophantine_context :
  -- Finding small nonzero values of |∑ δ_k/k| is a form of
  -- simultaneous Diophantine approximation problem
  True

/-!
## Part 7: Why the Problem is Hard
-/

/-- The search space is exponentially large -/
axiom exponential_search :
  -- There are 3^n choices for (δ_1, ..., δ_n)
  -- Brute force is infeasible for large n
  True

/-- Subtle cancellations required -/
axiom subtle_cancellations :
  -- Achieving small sums requires precise cancellation
  -- between terms with different denominators
  True

/-!
## Part 8: Related Problems
-/

/-- Egyptian fractions connection -/
axiom egyptian_fractions :
  -- Related to representing rationals as sums of distinct unit fractions
  -- Here we allow signs and repetitions (in a sense)
  True

/-- Connection to other Erdős problems on unit fractions -/
axiom related_erdos_problems :
  -- Problems #280, #281, etc. also concern unit fractions
  -- Different questions about the same arithmetic objects
  True

/-!
## Part 9: Summary
-/

/-- **Erdős Problem #317: OPEN**

QUESTION 1: Is there c > 0 such that for every n, we can achieve
0 < |∑_{k=1}^n δ_k/k| < c/2^n for some δ_k ∈ {-1, 0, 1}?

QUESTION 2: For large n, must any nonzero such sum exceed 1/lcm(1,...,n)?

KNOWN:
- Kovac-van Doorn: Weaker bound 2^{-n·polylog/log n} achievable
- van Doorn heuristic: This may be optimal (would make Q1 false)
- Q2 fails for small n (counterexample: 1/2 - 1/3 - 1/4 = -1/12)
- The weak inequality ≥ 1/lcm is trivial

The exact behavior of minimal signed unit fraction sums remains unknown.
-/
theorem erdos_317_status :
    -- Both questions remain OPEN
    True := trivial

/-- Problem status -/
def erdos_317_status_string : String :=
  "OPEN - Signed unit fraction approximation bounds"

end Erdos317
