import Proofs.Erdos85DegreeFourteenNormCertificate

/-!
# Executable primitive real norm certificates at degree twentysix

For the degree parameter `d = 26`, the frequency square scalar is
`25 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(25) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 653`) is checked by the native kernel evaluator.  The
Möbius divisor combinatorics (`moebiusPositiveDivisors`,
`moebiusNegativeDivisors`) is shared with the degree-fourteen certificate.

The designated square sector of degree `26` sits at conductor `4`,
where `R_4(25)` *is* a perfect square: the nonsquare certificate
therefore runs over the boundary range with conductor `4` removed,
while positivity (needed by the strong-induction cancellation) is
certified on the full range.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
`25`. -/
def chebyshevTwentyFiveLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevTwentyFiveLoop n current (25 * current - previous)

/-- The integer value `C_n(25)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=25`, `Cₙ₊₂=25Cₙ₊₁-Cₙ`. -/
def chebyshevTwentyFive (n : ℕ) : ℕ :=
  chebyshevTwentyFiveLoop n 2 25

/-- `P_n(25) = C_n(25)-2`. -/
def cycleChebyshevTwentyFive (n : ℕ) : ℕ := chebyshevTwentyFive n - 2

/-- Numerator in the multiplicative Möbius inversion of `P_n(25)`. -/
def primitiveRealNormSquareNumeratorTwentyFive (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevTwentyFive

/-- Denominator in the multiplicative Möbius inversion of `P_n(25)`. -/
def primitiveRealNormSquareDenominatorTwentyFive (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevTwentyFive

/-- Executable candidate for `R_n(25)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidateTwentyFive (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumeratorTwentyFive n /
    primitiveRealNormSquareDenominatorTwentyFive n

/-- Executable candidate for the primitive real norm `R_n(25)`. -/
def primitiveRealNormCandidateTwentyFive (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidateTwentyFive n)

/-- The rational-frequency factors: `25-2=23`, and additionally
`25-(-2)=27` for even cycle order. -/
def rationalCycleFrequencyFactorTwentyFive (n : ℕ) : ℕ :=
  23 * if n % 2 = 0 then 27 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProductTwentyFive (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidateTwentyFive k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidateTwentyFive_exact_division_upto_653 :
    ∀ n ∈ Finset.Icc 3 653,
      primitiveRealNormSquareCandidateTwentyFive n *
          primitiveRealNormSquareDenominatorTwentyFive n =
        primitiveRealNormSquareNumeratorTwentyFive n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidateTwentyFive` really is its certified square root. -/
theorem primitiveRealNormSquareCandidateTwentyFive_is_square_upto_653 :
    ∀ n ∈ Finset.Icc 3 653,
      primitiveRealNormCandidateTwentyFive n * primitiveRealNormCandidateTwentyFive n =
        primitiveRealNormSquareCandidateTwentyFive n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(25)-2 = 23 · (27 if 2∣n) · ∏_{k∣n, k≥3} R_k(25)^2`. -/
theorem cycleChebyshevTwentyFive_primitive_factorization_upto_653 :
    ∀ n ∈ Finset.Icc 3 653,
      cycleChebyshevTwentyFive n =
        rationalCycleFrequencyFactorTwentyFive n *
          primitiveRealNormDivisorProductTwentyFive n := by
  native_decide

/-- The primitive real norms are positive on the full boundary range,
including the designated conductor. -/
theorem primitiveRealNormCandidateTwentyFive_pos_upto_653 :
    ∀ n ∈ Finset.Icc 3 653, 0 < primitiveRealNormCandidateTwentyFive n := by
  native_decide

/-- Away from the designated conductor `4`, the primitive real norms are
never squares for `3 ≤ n ≤ 653`. -/
theorem primitiveRealNormCandidateTwentyFive_sqrt_ne_upto_653 :
    ∀ n ∈ (Finset.Icc 3 653).erase 4,
      Nat.sqrt (primitiveRealNormCandidateTwentyFive n) *
          Nat.sqrt (primitiveRealNormCandidateTwentyFive n) ≠
        primitiveRealNormCandidateTwentyFive n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidateTwentyFive_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn653 : n ≤ 653) (hn4 : n ≠ 4) :
    ¬ IsSquare (primitiveRealNormCandidateTwentyFive n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidateTwentyFive n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidateTwentyFive_sqrt_ne_upto_653 n
    (Finset.mem_erase.mpr ⟨hn4, Finset.mem_Icc.mpr ⟨hn3, hn653⟩⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
