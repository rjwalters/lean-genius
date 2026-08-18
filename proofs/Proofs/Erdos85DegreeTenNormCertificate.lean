import Proofs.Erdos85DegreeFourteenNormCertificate

/-!
# Executable primitive real norm certificates at degree ten

For the degree parameter `d = 10`, the frequency square scalar is
`9 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(9) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 93`) is checked by the native kernel evaluator.  The
Möbius divisor combinatorics (`moebiusPositiveDivisors`,
`moebiusNegativeDivisors`) is shared with the degree-fourteen certificate.

The designated square sector of degree `10` sits at conductor `4`,
where `R_4(9)` *is* a perfect square: the nonsquare certificate
therefore runs over the boundary range with conductor `4` removed,
while positivity (needed by the strong-induction cancellation) is
certified on the full range.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
`9`. -/
def chebyshevNineLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevNineLoop n current (9 * current - previous)

/-- The integer value `C_n(9)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=9`, `Cₙ₊₂=9Cₙ₊₁-Cₙ`. -/
def chebyshevNine (n : ℕ) : ℕ :=
  chebyshevNineLoop n 2 9

/-- `P_n(9) = C_n(9)-2`. -/
def cycleChebyshevNine (n : ℕ) : ℕ := chebyshevNine n - 2

/-- Numerator in the multiplicative Möbius inversion of `P_n(9)`. -/
def primitiveRealNormSquareNumeratorNine (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevNine

/-- Denominator in the multiplicative Möbius inversion of `P_n(9)`. -/
def primitiveRealNormSquareDenominatorNine (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevNine

/-- Executable candidate for `R_n(9)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidateNine (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumeratorNine n /
    primitiveRealNormSquareDenominatorNine n

/-- Executable candidate for the primitive real norm `R_n(9)`. -/
def primitiveRealNormCandidateNine (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidateNine n)

/-- The rational-frequency factors: `9-2=7`, and additionally
`9-(-2)=11` for even cycle order. -/
def rationalCycleFrequencyFactorNine (n : ℕ) : ℕ :=
  7 * if n % 2 = 0 then 11 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProductNine (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidateNine k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidateNine_exact_division_upto_93 :
    ∀ n ∈ Finset.Icc 3 93,
      primitiveRealNormSquareCandidateNine n *
          primitiveRealNormSquareDenominatorNine n =
        primitiveRealNormSquareNumeratorNine n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidateNine` really is its certified square root. -/
theorem primitiveRealNormSquareCandidateNine_is_square_upto_93 :
    ∀ n ∈ Finset.Icc 3 93,
      primitiveRealNormCandidateNine n * primitiveRealNormCandidateNine n =
        primitiveRealNormSquareCandidateNine n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(9)-2 = 7 · (11 if 2∣n) · ∏_{k∣n, k≥3} R_k(9)^2`. -/
theorem cycleChebyshevNine_primitive_factorization_upto_93 :
    ∀ n ∈ Finset.Icc 3 93,
      cycleChebyshevNine n =
        rationalCycleFrequencyFactorNine n *
          primitiveRealNormDivisorProductNine n := by
  native_decide

/-- The primitive real norms are positive on the full boundary range,
including the designated conductor. -/
theorem primitiveRealNormCandidateNine_pos_upto_93 :
    ∀ n ∈ Finset.Icc 3 93, 0 < primitiveRealNormCandidateNine n := by
  native_decide

/-- Away from the designated conductor `4`, the primitive real norms are
never squares for `3 ≤ n ≤ 93`. -/
theorem primitiveRealNormCandidateNine_sqrt_ne_upto_93 :
    ∀ n ∈ (Finset.Icc 3 93).erase 4,
      Nat.sqrt (primitiveRealNormCandidateNine n) *
          Nat.sqrt (primitiveRealNormCandidateNine n) ≠
        primitiveRealNormCandidateNine n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidateNine_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn93 : n ≤ 93) (hn4 : n ≠ 4) :
    ¬ IsSquare (primitiveRealNormCandidateNine n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidateNine n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidateNine_sqrt_ne_upto_93 n
    (Finset.mem_erase.mpr ⟨hn4, Finset.mem_Icc.mpr ⟨hn3, hn93⟩⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
