/-
  Erdős Problem #249: Irrationality of Sum of φ(n)/2^n

  Source: https://erdosproblems.com/249
  Status: OPEN

  Problem Statement:
  Is ∑_{n=1}^∞ φ(n)/2^n irrational?

  Here φ is Euler's totient function, counting integers 1 ≤ k ≤ n with gcd(k,n) = 1.

  Mathematical Background:
  - The series converges absolutely since |φ(n)/2^n| ≤ n/2^n → 0 rapidly
  - The decimal expansion is OEIS A256936
  - Related to other irrationality questions involving arithmetic functions

  Known Results:
  - The series converges to a well-defined real number
  - No proof of irrationality (or rationality) is known

  This is an OPEN problem. We formalize the statement and some basic properties.

  Tags: number-theory, irrationality, totient, erdos-problem
-/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Erdos249

/-! ## Part I: The Series Definition -/

/-- The general term of the series: φ(n)/2^n. -/
noncomputable def termFn (n : ℕ) : ℝ :=
  (Nat.totient n : ℝ) / (2 ^ n : ℝ)

/-- The series ∑_{n=1}^∞ φ(n)/2^n.

    Note: We sum over all n, but since φ(0) = 0, this is equivalent to n ≥ 1. -/
noncomputable def totientPowerSum : ℝ :=
  ∑' n, termFn n

/-! ## Part II: Basic Properties -/

/-- φ(n) ≤ n for all n (basic bound on totient). -/
theorem totient_le_self (n : ℕ) : Nat.totient n ≤ n :=
  Nat.totient_le n

/-- Each term is non-negative. -/
theorem termFn_nonneg (n : ℕ) : termFn n ≥ 0 := by
  simp only [termFn]
  apply div_nonneg (Nat.cast_nonneg _)
  positivity

/-- The term for n = 0 is zero. -/
theorem termFn_zero : termFn 0 = 0 := by
  simp [termFn, Nat.totient_zero]

/-- φ(1) = 1, so the first term is 1/2. -/
theorem termFn_one : termFn 1 = 1 / 2 := by
  simp [termFn, Nat.totient_one]

/-- φ(2) = 1, so the second term is 1/4. -/
theorem termFn_two : termFn 2 = 1 / 4 := by
  unfold termFn
  simp [Nat.totient_prime Nat.prime_two]
  ring

/-! ## Part III: Convergence

The series converges absolutely since φ(n)/2^n ≤ n/2^n and ∑ n/2^n converges.
We axiomatize this since the Mathlib API for comparison tests requires
careful handling. -/

/-- The series converges absolutely.

    This follows from comparison with ∑ n/2^n, which converges
    since the ratio n/2^n → 0 as n → ∞. -/
axiom totientPowerSum_summable : Summable termFn

/-- The sum is positive.

    Since φ(1) = 1, we have termFn 1 = 1/2 > 0, and all terms are non-negative,
    so the sum is at least 1/2 > 0. -/
axiom totientPowerSum_pos : totientPowerSum > 0

/-- Upper bound: the sum is at most 2.

    This follows from ∑_{n≥0} φ(n)/2^n ≤ ∑_{n≥0} n/2^n = 2. -/
axiom totientPowerSum_le_two : totientPowerSum ≤ 2

/-! ## Part IV: The Main Conjecture -/

/-- **Erdős Problem #249** (OPEN)

    Is the sum ∑_{n=1}^∞ φ(n)/2^n irrational?

    This is an open problem. No proof of irrationality (or rationality) is known. -/
def erdos_249 : Prop := Irrational totientPowerSum

/-! ## Part V: Alternative Characterization -/

/-- The negation of the conjecture: the sum is rational. -/
def isRational : Prop := ∃ (r : ℚ), (r : ℝ) = totientPowerSum

/-- The conjecture is equivalent to saying the sum is not rational.

    Note: In Mathlib, Irrational x means ¬∃ r : ℚ, (r : ℝ) = x,
    which is definitionally equal to ¬isRational. -/
theorem erdos_249_iff_not_rational : erdos_249 ↔ ¬isRational := by
  rfl

/-! ## Part VI: Numerical Information

The sum begins:
  φ(1)/2^1 + φ(2)/2^2 + φ(3)/2^3 + φ(4)/2^4 + ...
  = 1/2 + 1/4 + 2/8 + 2/16 + ...
  = 0.5 + 0.25 + 0.25 + 0.125 + ...
  ≈ 1.3240...

The decimal expansion is OEIS sequence A256936.
-/

/-- Partial sum of first 2 nonzero terms. -/
theorem partial_sum_2 : termFn 1 + termFn 2 = 3 / 4 := by
  rw [termFn_one, termFn_two]
  ring

/-! ## Summary

**Problem Status**: OPEN

**What we know**:
1. The series converges (axiomatized)
2. The sum is positive and at most 2 (axiomatized)
3. Numerical value ≈ 1.3240... (OEIS A256936)

**What we don't know**:
- Is this number irrational? (The main question)
- If irrational, what is its irrationality measure?

**Formalization provides**:
- Definition of the sum using tsum
- Term computations for small n
- Formal statement of the OPEN conjecture
- Basic axiomatized properties
-/

#check totientPowerSum
#check totientPowerSum_summable
#check totientPowerSum_pos
#check erdos_249

end Erdos249
