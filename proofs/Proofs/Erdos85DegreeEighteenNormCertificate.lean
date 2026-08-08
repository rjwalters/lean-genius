import Proofs.Erdos85DegreeFourteenNormCertificate

/-!
# Executable primitive real norm certificates at degree eighteen

For the degree parameter `d = 18`, the frequency square scalar is
`17 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(17) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 309`) is checked by the native kernel evaluator.  The
Möbius divisor combinatorics (`moebiusPositiveDivisors`,
`moebiusNegativeDivisors`) is shared with the degree-fourteen certificate.

The designated square sector of degree `18` sits at conductor `6`,
where `R_6(17)` *is* a perfect square: the nonsquare certificate
therefore runs over the boundary range with conductor `6` removed,
while positivity (needed by the strong-induction cancellation) is
certified on the full range.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
`17`. -/
def chebyshevSeventeenLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevSeventeenLoop n current (17 * current - previous)

/-- The integer value `C_n(17)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=17`, `Cₙ₊₂=17Cₙ₊₁-Cₙ`. -/
def chebyshevSeventeen (n : ℕ) : ℕ :=
  chebyshevSeventeenLoop n 2 17

/-- `P_n(17) = C_n(17)-2`. -/
def cycleChebyshevSeventeen (n : ℕ) : ℕ := chebyshevSeventeen n - 2

/-- Numerator in the multiplicative Möbius inversion of `P_n(17)`. -/
def primitiveRealNormSquareNumeratorSeventeen (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevSeventeen

/-- Denominator in the multiplicative Möbius inversion of `P_n(17)`. -/
def primitiveRealNormSquareDenominatorSeventeen (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevSeventeen

/-- Executable candidate for `R_n(17)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidateSeventeen (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumeratorSeventeen n /
    primitiveRealNormSquareDenominatorSeventeen n

/-- Executable candidate for the primitive real norm `R_n(17)`. -/
def primitiveRealNormCandidateSeventeen (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidateSeventeen n)

/-- The rational-frequency factors: `17-2=15`, and additionally
`17-(-2)=19` for even cycle order. -/
def rationalCycleFrequencyFactorSeventeen (n : ℕ) : ℕ :=
  15 * if n % 2 = 0 then 19 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProductSeventeen (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidateSeventeen k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidateSeventeen_exact_division_upto_309 :
    ∀ n ∈ Finset.Icc 3 309,
      primitiveRealNormSquareCandidateSeventeen n *
          primitiveRealNormSquareDenominatorSeventeen n =
        primitiveRealNormSquareNumeratorSeventeen n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidateSeventeen` really is its certified square root. -/
theorem primitiveRealNormSquareCandidateSeventeen_is_square_upto_309 :
    ∀ n ∈ Finset.Icc 3 309,
      primitiveRealNormCandidateSeventeen n * primitiveRealNormCandidateSeventeen n =
        primitiveRealNormSquareCandidateSeventeen n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(17)-2 = 15 · (19 if 2∣n) · ∏_{k∣n, k≥3} R_k(17)^2`. -/
theorem cycleChebyshevSeventeen_primitive_factorization_upto_309 :
    ∀ n ∈ Finset.Icc 3 309,
      cycleChebyshevSeventeen n =
        rationalCycleFrequencyFactorSeventeen n *
          primitiveRealNormDivisorProductSeventeen n := by
  native_decide

/-- The primitive real norms are positive on the full boundary range,
including the designated conductor. -/
theorem primitiveRealNormCandidateSeventeen_pos_upto_309 :
    ∀ n ∈ Finset.Icc 3 309, 0 < primitiveRealNormCandidateSeventeen n := by
  native_decide

/-- Away from the designated conductor `6`, the primitive real norms are
never squares for `3 ≤ n ≤ 309`. -/
theorem primitiveRealNormCandidateSeventeen_sqrt_ne_upto_309 :
    ∀ n ∈ (Finset.Icc 3 309).erase 6,
      Nat.sqrt (primitiveRealNormCandidateSeventeen n) *
          Nat.sqrt (primitiveRealNormCandidateSeventeen n) ≠
        primitiveRealNormCandidateSeventeen n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidateSeventeen_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn309 : n ≤ 309) (hn6 : n ≠ 6) :
    ¬ IsSquare (primitiveRealNormCandidateSeventeen n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidateSeventeen n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidateSeventeen_sqrt_ne_upto_309 n
    (Finset.mem_erase.mpr ⟨hn6, Finset.mem_Icc.mpr ⟨hn3, hn309⟩⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
