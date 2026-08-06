import Proofs.Erdos85DegreeFourteenNormCertificate

/-!
# Executable primitive real norm certificates at degree thirty-four

For the degree parameter `d = 34`, the frequency square scalar is
`33 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is obtained
without constructing a cyclotomic field: Möbius inversion applied to
`P n = C_n(33) - 2` isolates the square of that norm.

Everything in this file is executable.  The range needed at the exact
boundary (`3 ≤ n ≤ 1125`) is checked by the native kernel evaluator.  The
Möbius divisor combinatorics (`moebiusPositiveDivisors`,
`moebiusNegativeDivisors`) is shared with the degree-fourteen certificate.

The degree-`26` analogue is arithmetically blocked: there
`R_4(25) = 25 = 5²` is a perfect square (the conductor-four trace is
`μ = 0`, whose norm at `25` is `25` itself), so no nonsquare certificate
exists at that degree.  At `33` the conductor-four norm is `33 = 3 · 11`,
squarefree hence nonsquare, and the whole boundary range is certified
nonsquare below.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
`33`. -/
def chebyshevThirtyThreeLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevThirtyThreeLoop n current (33 * current - previous)

/-- The integer value `C_n(33)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=33`, `Cₙ₊₂=33Cₙ₊₁-Cₙ`. -/
def chebyshevThirtyThree (n : ℕ) : ℕ :=
  chebyshevThirtyThreeLoop n 2 33

/-- `P_n(33) = C_n(33)-2`. -/
def cycleChebyshevThirtyThree (n : ℕ) : ℕ := chebyshevThirtyThree n - 2

/-- Numerator in the multiplicative Möbius inversion of `P_n(33)`. -/
def primitiveRealNormSquareNumeratorThirtyThree (n : ℕ) : ℕ :=
  (moebiusPositiveDivisors n).prod cycleChebyshevThirtyThree

/-- Denominator in the multiplicative Möbius inversion of `P_n(33)`. -/
def primitiveRealNormSquareDenominatorThirtyThree (n : ℕ) : ℕ :=
  (moebiusNegativeDivisors n).prod cycleChebyshevThirtyThree

/-- Executable candidate for `R_n(33)^2`.  The exact-division certificate
below verifies that the quotient has no truncation in the required range. -/
def primitiveRealNormSquareCandidateThirtyThree (n : ℕ) : ℕ :=
  primitiveRealNormSquareNumeratorThirtyThree n /
    primitiveRealNormSquareDenominatorThirtyThree n

/-- Executable candidate for the primitive real norm `R_n(33)`. -/
def primitiveRealNormCandidateThirtyThree (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveRealNormSquareCandidateThirtyThree n)

/-- The rational-frequency factors: `33-2=31`, and additionally
`33-(-2)=35` for even cycle order. -/
def rationalCycleFrequencyFactorThirtyThree (n : ℕ) : ℕ :=
  31 * if n % 2 = 0 then 35 else 1

/-- Product of the primitive real norm squares over conductors dividing
`n`, with the trivial conductors one and two removed. -/
def primitiveRealNormDivisorProductThirtyThree (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun k => k ∣ n).prod fun k =>
    primitiveRealNormCandidateThirtyThree k ^ 2

/-- In the complete exact-boundary range, the Möbius denominator divides
the numerator exactly. -/
theorem primitiveRealNormSquareCandidateThirtyThree_exact_division_upto_1125 :
    ∀ n ∈ Finset.Icc 3 1125,
      primitiveRealNormSquareCandidateThirtyThree n *
          primitiveRealNormSquareDenominatorThirtyThree n =
        primitiveRealNormSquareNumeratorThirtyThree n := by
  native_decide

/-- Every Möbius quotient in the complete range is a perfect square, so
`primitiveRealNormCandidateThirtyThree` really is its certified square
root. -/
theorem primitiveRealNormSquareCandidateThirtyThree_is_square_upto_1125 :
    ∀ n ∈ Finset.Icc 3 1125,
      primitiveRealNormCandidateThirtyThree n *
          primitiveRealNormCandidateThirtyThree n =
        primitiveRealNormSquareCandidateThirtyThree n := by
  native_decide

/-- Certified multiplicity table for the cycle polynomial:
`C_n(33)-2 = 31 · (35 if 2∣n) · ∏_{k∣n, k≥3} R_k(33)^2`.
In particular every nonrational primitive real factor occurs with the
mathematically required multiplicity two. -/
theorem cycleChebyshevThirtyThree_primitive_factorization_upto_1125 :
    ∀ n ∈ Finset.Icc 3 1125,
      cycleChebyshevThirtyThree n =
        rationalCycleFrequencyFactorThirtyThree n *
          primitiveRealNormDivisorProductThirtyThree n := by
  native_decide

/-- The primitive real norms themselves are never squares for
`3 ≤ n ≤ 1125`. -/
theorem primitiveRealNormCandidateThirtyThree_sqrt_ne_upto_1125 :
    ∀ n ∈ Finset.Icc 3 1125,
      Nat.sqrt (primitiveRealNormCandidateThirtyThree n) *
          Nat.sqrt (primitiveRealNormCandidateThirtyThree n) ≠
        primitiveRealNormCandidateThirtyThree n := by
  native_decide

/-- Proposition-level form of the native nonsquare certificate. -/
theorem primitiveRealNormCandidateThirtyThree_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn1125 : n ≤ 1125) :
    ¬ IsSquare (primitiveRealNormCandidateThirtyThree n) := by
  intro hsq
  obtain ⟨a, ha⟩ := hsq
  have hsqrt : Nat.sqrt (primitiveRealNormCandidateThirtyThree n) = a := by
    rw [ha]
    simpa [pow_two] using Nat.sqrt_eq a
  have hne := primitiveRealNormCandidateThirtyThree_sqrt_ne_upto_1125 n
    (Finset.mem_Icc.mpr ⟨hn3, hn1125⟩)
  apply hne
  rw [hsqrt]
  exact ha.symm

end Erdos85
