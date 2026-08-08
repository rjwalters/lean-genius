import Proofs.Erdos85DegreeFourteenNormCertificate

/-!
# Executable primitive real norm certificates at degree twenty-two

For the degree parameter `d = 22`, the frequency square scalar is
`21 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(21) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 465`) is checked by the native kernel evaluator.  The
Möbius divisor combinatorics (`moebiusPositiveDivisors`,
`moebiusNegativeDivisors`) is shared with the degree-fourteen certificate.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
`21`. -/
def chebyshevTwentyOneLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevTwentyOneLoop n current (21 * current - previous)

/-- The integer value `C_n(21)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=21`, `Cₙ₊₂=21Cₙ₊₁-Cₙ`. -/
def chebyshevTwentyOne (n : ℕ) : ℕ :=
  chebyshevTwentyOneLoop n 2 21

/-- `P_n(21) = C_n(21)-2`. -/
def cycleChebyshevTwentyOne (n : ℕ) : ℕ := chebyshevTwentyOne n - 2

/-- Numerator in the multiplicative Möbius inversion of `P_n(21)`. -/
def primitiveRealNormSquareNumeratorTwentyOne (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevTwentyOne

/-- Denominator in the multiplicative Möbius inversion of `P_n(21)`. -/
def primitiveRealNormSquareDenominatorTwentyOne (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevTwentyOne

/-- Executable candidate for `R_n(21)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidateTwentyOne (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumeratorTwentyOne n /
    primitiveRealNormSquareDenominatorTwentyOne n

/-- Executable candidate for the primitive real norm `R_n(21)`. -/
def primitiveRealNormCandidateTwentyOne (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidateTwentyOne n)

/-- The rational-frequency factors: `21-2=19`, and additionally
`21-(-2)=23` for even cycle order. -/
def rationalCycleFrequencyFactorTwentyOne (n : ℕ) : ℕ :=
  19 * if n % 2 = 0 then 23 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProductTwentyOne (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidateTwentyOne k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidateTwentyOne_exact_division_upto_465 :
    ∀ n ∈ Finset.Icc 3 465,
      primitiveRealNormSquareCandidateTwentyOne n *
          primitiveRealNormSquareDenominatorTwentyOne n =
        primitiveRealNormSquareNumeratorTwentyOne n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidateTwentyOne` really is its certified square
root. -/
theorem primitiveRealNormSquareCandidateTwentyOne_is_square_upto_465 :
    ∀ n ∈ Finset.Icc 3 465,
      primitiveRealNormCandidateTwentyOne n *
          primitiveRealNormCandidateTwentyOne n =
        primitiveRealNormSquareCandidateTwentyOne n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(21)-2 = 19 · (23 if 2∣n) · ∏_{k∣n, k≥3} R_k(21)^2`.
In particular every nonrational primitive real factor occurs with the
mathematically required multiplicity two. -/
theorem cycleChebyshevTwentyOne_primitive_factorization_upto_465 :
    ∀ n ∈ Finset.Icc 3 465,
      cycleChebyshevTwentyOne n =
        rationalCycleFrequencyFactorTwentyOne n *
          primitiveRealNormDivisorProductTwentyOne n := by
  native_decide

/-- The primitive real norms themselves are never squares for
`3 ≤ n ≤ 465`. -/
theorem primitiveRealNormCandidateTwentyOne_sqrt_ne_upto_465 :
    ∀ n ∈ Finset.Icc 3 465,
      Nat.sqrt (primitiveRealNormCandidateTwentyOne n) *
          Nat.sqrt (primitiveRealNormCandidateTwentyOne n) ≠
        primitiveRealNormCandidateTwentyOne n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidateTwentyOne_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn465 : n ≤ 465) :
    ¬ IsSquare (primitiveRealNormCandidateTwentyOne n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidateTwentyOne n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidateTwentyOne_sqrt_ne_upto_465 n
    (Finset.mem_Icc.mpr ⟨hn3, hn465⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
