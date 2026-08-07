import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Sqrt

/-!
# Executable primitive real norm certificates at parameter `123`

For the saturated residual at degree `d = 124`, the frequency square
scalar is `123 - (ζ + ζ⁻¹)`.  Its primitive real norm at conductor `n` is
obtained without constructing a cyclotomic field: Möbius inversion applied
to `P n = C_n(123) - 2` isolates the square of that norm.

The rational factors are `123 - 2 = 121 = 11²` (the designated square
sector, root `11`) and, for even conductors, `123 + 2 = 125 = 5³`.

Everything in this file is executable.  The exterior range
`3 ≤ n ≤ 15120` is verified by the native kernel evaluator in blocks.
-/

namespace Erdos85

open scoped ArithmeticFunction.Moebius

/-- Tail-recursive evaluator for the normalized Chebyshev recurrence at
parameter `123`. -/
def chebyshevOneTwentyThreeLoop : ℕ → ℕ → ℕ → ℕ
  | 0, previous, _ => previous
  | n + 1, previous, current =>
      chebyshevOneTwentyThreeLoop n current (123 * current - previous)

/-- The integer value `C_n(123)` of the normalized Chebyshev polynomial,
computed by `C₀=2`, `C₁=123`, `Cₙ₊₂=123Cₙ₊₁-Cₙ`. -/
def chebyshevOneTwentyThree (n : ℕ) : ℕ :=
  chebyshevOneTwentyThreeLoop n 2 123

/-- `P_n(123) = C_n(123)-2`. -/
def cycleChebyshevOneTwentyThree (n : ℕ) : ℕ :=
  chebyshevOneTwentyThree n - 2

/-- Divisors whose complementary divisor has Möbius value `+1`. -/
def moebiusPositiveDivisorsOTT (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k =>
    k ∣ n ∧ ArithmeticFunction.moebius (n / k) = 1

/-- Divisors whose complementary divisor has Möbius value `-1`. -/
def moebiusNegativeDivisorsOTT (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k =>
    k ∣ n ∧ ArithmeticFunction.moebius (n / k) = -1

/-- Numerator in the multiplicative Möbius inversion of `P_n(123)`. -/
def primitiveNormSquareNumeratorOTT (n : ℕ) : ℕ :=
  (moebiusPositiveDivisorsOTT n).prod cycleChebyshevOneTwentyThree

/-- Denominator in the multiplicative Möbius inversion of `P_n(123)`. -/
def primitiveNormSquareDenominatorOTT (n : ℕ) : ℕ :=
  (moebiusNegativeDivisorsOTT n).prod cycleChebyshevOneTwentyThree

/-- Executable candidate for `R_n(123)^2`. -/
def primitiveNormSquareCandidateOTT (n : ℕ) : ℕ :=
  primitiveNormSquareNumeratorOTT n /
    primitiveNormSquareDenominatorOTT n

/-- Executable candidate for the primitive real norm `R_n(123)`. -/
def primitiveNormCandidateOTT (n : ℕ) : ℕ :=
  Nat.sqrt (primitiveNormSquareCandidateOTT n)

/-- Single-conductor certificate: the Möbius quotient is exact, its value
is the square of the certified root, and that root is not itself a
square. -/
def normCertificateOTT (n : ℕ) : Bool :=
  let den := primitiveNormSquareDenominatorOTT n
  let num := primitiveNormSquareNumeratorOTT n
  let q := num / den
  let r := Nat.sqrt q
  q * den == num && r * r == q &&
    Nat.sqrt r * Nat.sqrt r != r

/-- Block-range certificate runner. -/
def normCertificateRangeOTT (lo hi : ℕ) : Bool :=
  (List.range' lo (hi + 1 - lo)).all normCertificateOTT

/-- Blocks `3–2000`. -/
theorem normCertificateRangeOTT_block1 :
    normCertificateRangeOTT 3 2000 = true := by
  native_decide

/-- Blocks `2001–6000`. -/
theorem normCertificateRangeOTT_block2 :
    normCertificateRangeOTT 2001 6000 = true := by
  native_decide

/-- Blocks `6001–10000`. -/
theorem normCertificateRangeOTT_block3 :
    normCertificateRangeOTT 6001 10000 = true := by
  native_decide

/-- Blocks `10001–13000`. -/
theorem normCertificateRangeOTT_block4 :
    normCertificateRangeOTT 10001 13000 = true := by
  native_decide

/-- Blocks `13001–15255`, covering the full parent boundary as well as
the exterior order. -/
theorem normCertificateRangeOTT_block5 :
    normCertificateRangeOTT 13001 15255 = true := by
  native_decide

/-- Propositional consequence of a verified block: on that range, the
Möbius quotient is exact, `primitiveNormCandidateOTT` is its certified
square root, and the primitive norms are never squares. -/
theorem primitiveNormCandidateOTT_not_isSquare_of_block
    {lo hi n : ℕ} (hblock : normCertificateRangeOTT lo hi = true)
    (hlo : lo ≤ n) (hhi : n ≤ hi) :
    primitiveNormCandidateOTT n * primitiveNormCandidateOTT n =
        primitiveNormSquareCandidateOTT n ∧
      ¬ IsSquare (primitiveNormCandidateOTT n) := by
  have hmem : n ∈ List.range' lo (hi + 1 - lo) := by
    rw [List.mem_range'_1]
    exact ⟨hlo, by omega⟩
  have hcert : normCertificateOTT n = true := by
    have hall := hblock
    rw [normCertificateRangeOTT, List.all_eq_true] at hall
    exact hall n hmem
  rw [normCertificateOTT] at hcert
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hcert
  obtain ⟨⟨hdiv, hsq⟩, hnsq⟩ := hcert
  refine ⟨hsq, ?_⟩
  intro hsquare
  obtain ⟨a, ha⟩ := hsquare
  apply hnsq
  have ha' : Nat.sqrt (primitiveNormSquareNumeratorOTT n /
      primitiveNormSquareDenominatorOTT n) = a * a := ha
  have hs : Nat.sqrt (a * a) = a := by
    simpa [pow_two] using Nat.sqrt_eq a
  rw [ha', hs]

/-- **The full-range norm certificate.**  For every conductor
`3 ≤ n ≤ 15255` (covering both the exterior order `15120` and the full
parent boundary `15255`), the Möbius quotient of the cycle values
`C_k(123) - 2` is an exact perfect square, and its certified square root
— the primitive real norm of `123 - (ζₙ + ζₙ⁻¹)` — is NOT a square. -/
theorem primitiveNormOTT_not_isSquare
    {n : ℕ} (hn3 : 3 ≤ n) (hn : n ≤ 15255) :
    primitiveNormCandidateOTT n * primitiveNormCandidateOTT n =
        primitiveNormSquareCandidateOTT n ∧
      ¬ IsSquare (primitiveNormCandidateOTT n) := by
  by_cases h : n ≤ 2000
  · exact primitiveNormCandidateOTT_not_isSquare_of_block
      normCertificateRangeOTT_block1 hn3 h
  by_cases h2 : n ≤ 6000
  · exact primitiveNormCandidateOTT_not_isSquare_of_block
      normCertificateRangeOTT_block2 (by omega) h2
  by_cases h3 : n ≤ 10000
  · exact primitiveNormCandidateOTT_not_isSquare_of_block
      normCertificateRangeOTT_block3 (by omega) h3
  by_cases h4 : n ≤ 13000
  · exact primitiveNormCandidateOTT_not_isSquare_of_block
      normCertificateRangeOTT_block4 (by omega) h4
  · exact primitiveNormCandidateOTT_not_isSquare_of_block
      normCertificateRangeOTT_block5 (by omega) hn

end Erdos85
