import Proofs.Erdos85DegreeFourteenNormCertificate

/-!
# Executable primitive real norm certificates at degree thirty

For the degree parameter `d = 30`, the frequency square scalar is
`29 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(29) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 873`) is checked by the native kernel evaluator.  The
Möbius divisor combinatorics (`moebiusPositiveDivisors`,
`moebiusNegativeDivisors`) is shared with the degree-fourteen certificate.

The degree-`26` analogue is arithmetically blocked: there
`R_4(25) = 25 = 5²` is a perfect square (the conductor-four trace is
`μ = 0`, whose norm at `25` is `25` itself), so no nonsquare certificate
exists at that degree.  At `29` the conductor-four norm is the prime `29`
and the whole boundary range is certified nonsquare below.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
`29`. -/
def chebyshevTwentyNineLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevTwentyNineLoop n current (29 * current - previous)

/-- The integer value `C_n(29)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=29`, `Cₙ₊₂=29Cₙ₊₁-Cₙ`. -/
def chebyshevTwentyNine (n : ℕ) : ℕ :=
  chebyshevTwentyNineLoop n 2 29

/-- `P_n(29) = C_n(29)-2`. -/
def cycleChebyshevTwentyNine (n : ℕ) : ℕ := chebyshevTwentyNine n - 2

/-- Numerator in the multiplicative Möbius inversion of `P_n(29)`. -/
def primitiveRealNormSquareNumeratorTwentyNine (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevTwentyNine

/-- Denominator in the multiplicative Möbius inversion of `P_n(29)`. -/
def primitiveRealNormSquareDenominatorTwentyNine (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevTwentyNine

/-- Executable candidate for `R_n(29)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidateTwentyNine (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumeratorTwentyNine n /
    primitiveRealNormSquareDenominatorTwentyNine n

/-- Executable candidate for the primitive real norm `R_n(29)`. -/
def primitiveRealNormCandidateTwentyNine (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidateTwentyNine n)

/-- The rational-frequency factors: `29-2=27`, and additionally
`29-(-2)=31` for even cycle order. -/
def rationalCycleFrequencyFactorTwentyNine (n : ℕ) : ℕ :=
  27 * if n % 2 = 0 then 31 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProductTwentyNine (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidateTwentyNine k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidateTwentyNine_exact_division_upto_873 :
    ∀ n ∈ Finset.Icc 3 873,
      primitiveRealNormSquareCandidateTwentyNine n *
          primitiveRealNormSquareDenominatorTwentyNine n =
        primitiveRealNormSquareNumeratorTwentyNine n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidateTwentyNine` really is its certified square
root. -/
theorem primitiveRealNormSquareCandidateTwentyNine_is_square_upto_873 :
    ∀ n ∈ Finset.Icc 3 873,
      primitiveRealNormCandidateTwentyNine n *
          primitiveRealNormCandidateTwentyNine n =
        primitiveRealNormSquareCandidateTwentyNine n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(29)-2 = 27 · (31 if 2∣n) · ∏_{k∣n, k≥3} R_k(29)^2`.
In particular every nonrational primitive real factor occurs with the
mathematically required multiplicity two. -/
theorem cycleChebyshevTwentyNine_primitive_factorization_upto_873 :
    ∀ n ∈ Finset.Icc 3 873,
      cycleChebyshevTwentyNine n =
        rationalCycleFrequencyFactorTwentyNine n *
          primitiveRealNormDivisorProductTwentyNine n := by
  native_decide

/-- The primitive real norms themselves are never squares for
`3 ≤ n ≤ 873`. -/
theorem primitiveRealNormCandidateTwentyNine_sqrt_ne_upto_873 :
    ∀ n ∈ Finset.Icc 3 873,
      Nat.sqrt (primitiveRealNormCandidateTwentyNine n) *
          Nat.sqrt (primitiveRealNormCandidateTwentyNine n) ≠
        primitiveRealNormCandidateTwentyNine n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidateTwentyNine_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn873 : n ≤ 873) :
    ¬ IsSquare (primitiveRealNormCandidateTwentyNine n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidateTwentyNine n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidateTwentyNine_sqrt_ne_upto_873 n
    (Finset.mem_Icc.mpr ⟨hn3, hn873⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
