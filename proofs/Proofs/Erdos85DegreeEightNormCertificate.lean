import Proofs.Erdos85DegreeFourteenNormCertificate

/-!
# Executable primitive real norm certificates at degree eight

For the degree parameter `d = 8`, the frequency square scalar is
`7 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(7) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 59`) is checked by the native kernel evaluator.  The
Möbius divisor combinatorics (`moebiusPositiveDivisors`,
`moebiusNegativeDivisors`) is shared with the degree-fourteen certificate.

At degree eight the designated square sector sits at conductor two
(`μ₀ = -2`, value `7 + 2 = 9 = 3²`), which is a rational conductor and
therefore outside the primitive table `3 ≤ n`: the entire boundary range
is certified nonsquare with no exception.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
`7`. -/
def chebyshevSevenLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevSevenLoop n current (7 * current - previous)

/-- The integer value `C_n(7)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=7`, `Cₙ₊₂=7Cₙ₊₁-Cₙ`. -/
def chebyshevSeven (n : ℕ) : ℕ :=
  chebyshevSevenLoop n 2 7

/-- `P_n(7) = C_n(7)-2`. -/
def cycleChebyshevSeven (n : ℕ) : ℕ := chebyshevSeven n - 2

/-- Numerator in the multiplicative Möbius inversion of `P_n(7)`. -/
def primitiveRealNormSquareNumeratorSeven (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevSeven

/-- Denominator in the multiplicative Möbius inversion of `P_n(7)`. -/
def primitiveRealNormSquareDenominatorSeven (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevSeven

/-- Executable candidate for `R_n(7)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidateSeven (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumeratorSeven n /
    primitiveRealNormSquareDenominatorSeven n

/-- Executable candidate for the primitive real norm `R_n(7)`. -/
def primitiveRealNormCandidateSeven (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidateSeven n)

/-- The rational-frequency factors: `7-2=5`, and additionally
`7-(-2)=9` for even cycle order. -/
def rationalCycleFrequencyFactorSeven (n : ℕ) : ℕ :=
  5 * if n % 2 = 0 then 9 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProductSeven (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidateSeven k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidateSeven_exact_division_upto_59 :
    ∀ n ∈ Finset.Icc 3 59,
      primitiveRealNormSquareCandidateSeven n *
          primitiveRealNormSquareDenominatorSeven n =
        primitiveRealNormSquareNumeratorSeven n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidateSeven` really is its certified square
root. -/
theorem primitiveRealNormSquareCandidateSeven_is_square_upto_59 :
    ∀ n ∈ Finset.Icc 3 59,
      primitiveRealNormCandidateSeven n *
          primitiveRealNormCandidateSeven n =
        primitiveRealNormSquareCandidateSeven n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(7)-2 = 5 · (9 if 2∣n) · ∏_{k∣n, k≥3} R_k(7)^2`.
In particular every nonrational primitive real factor occurs with the
mathematically required multiplicity two. -/
theorem cycleChebyshevSeven_primitive_factorization_upto_59 :
    ∀ n ∈ Finset.Icc 3 59,
      cycleChebyshevSeven n =
        rationalCycleFrequencyFactorSeven n *
          primitiveRealNormDivisorProductSeven n := by
  native_decide

/-- The primitive real norms themselves are never squares for
`3 ≤ n ≤ 59`. -/
theorem primitiveRealNormCandidateSeven_sqrt_ne_upto_59 :
    ∀ n ∈ Finset.Icc 3 59,
      Nat.sqrt (primitiveRealNormCandidateSeven n) *
          Nat.sqrt (primitiveRealNormCandidateSeven n) ≠
        primitiveRealNormCandidateSeven n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidateSeven_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn59 : n ≤ 59) :
    ¬ IsSquare (primitiveRealNormCandidateSeven n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidateSeven n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidateSeven_sqrt_ne_upto_59 n
    (Finset.mem_Icc.mpr ⟨hn3, hn59⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
