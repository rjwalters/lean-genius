import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Sqrt

/-!
# Executable primitive real norm certificates at degree fourteen

For the degree parameter `d = 14`, the frequency square scalar is
`13 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(13) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 185`) is checked by the native kernel evaluator.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence. -/
def chebyshevThirteenLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevThirteenLoop n current (13 * current - previous)

/-- The integer value `C_n(13)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=13`, `Cₙ₊₂=13Cₙ₊₁-Cₙ`. -/
def chebyshevThirteen (n : ℕ) : ℕ :=
  chebyshevThirteenLoop n 2 13

/-- `P_n(13) = C_n(13)-2`. -/
def cycleChebyshevThirteen (n : ℕ) : ℕ := chebyshevThirteen n - 2

/-- Divisors whose complementary divisor has Möbius value `+1`. -/
def moebiusPositiveDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k =>
    k ∣ n ∧ ArithmeticFunction.moebius (n / k) = 1

/-- Divisors whose complementary divisor has Möbius value `-1`. -/
def moebiusNegativeDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k =>
    k ∣ n ∧ ArithmeticFunction.moebius (n / k) = -1

/-- Numerator in the multiplicative Möbius inversion of `P_n(13)`. -/
def primitiveRealNormSquareNumerator (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevThirteen

/-- Denominator in the multiplicative Möbius inversion of `P_n(13)`. -/
def primitiveRealNormSquareDenominator (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevThirteen

/-- Executable candidate for `R_n(13)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidate (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumerator n /
    primitiveRealNormSquareDenominator n

/-- Executable candidate for the primitive real norm `R_n(13)`. -/
def primitiveRealNormCandidate (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidate n)

/-- The rational-frequency factors: `13-2=11`, and additionally
`13-(-2)=15` for even cycle order. -/
def rationalCycleFrequencyFactor (n : ℕ) : ℕ :=
  11 * if n % 2 = 0 then 15 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProduct (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidate k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidate_exact_division_upto_185 :
    ∀ n ∈ Finset.Icc 3 185,
      primitiveRealNormSquareCandidate n *
          primitiveRealNormSquareDenominator n =
        primitiveRealNormSquareNumerator n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidate` really is its certified square root. -/
theorem primitiveRealNormSquareCandidate_is_square_upto_185 :
    ∀ n ∈ Finset.Icc 3 185,
      primitiveRealNormCandidate n * primitiveRealNormCandidate n =
        primitiveRealNormSquareCandidate n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(13)-2 = 11 · (15 if 2∣n) · ∏_{k∣n, k≥3} R_k(13)^2`.
In particular every nonrational primitive real factor occurs with the
mathematically required multiplicity two. -/
theorem cycleChebyshevThirteen_primitive_factorization_upto_185 :
    ∀ n ∈ Finset.Icc 3 185,
      cycleChebyshevThirteen n =
        rationalCycleFrequencyFactor n *
          primitiveRealNormDivisorProduct n := by
  native_decide

/-- The primitive real norms themselves are never squares for
`3 ≤ n ≤ 185`. -/
theorem primitiveRealNormCandidate_sqrt_ne_upto_185 :
    ∀ n ∈ Finset.Icc 3 185,
      Nat.sqrt (primitiveRealNormCandidate n) *
          Nat.sqrt (primitiveRealNormCandidate n) ≠
        primitiveRealNormCandidate n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidate_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn185 : n ≤ 185) :
    ¬ IsSquare (primitiveRealNormCandidate n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidate n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidate_sqrt_ne_upto_185 n
    (Finset.mem_Icc.mpr ⟨hn3, hn185⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
