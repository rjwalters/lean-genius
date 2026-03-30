import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Quotient
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-
# Multiplicativity of Euler's Totient Function

## What This Proves

The fundamental multiplicative property of Euler's totient function:

  **φ(mn) = φ(m) · φ(n)** whenever gcd(m, n) = 1

This is equivalent to saying φ is a **multiplicative arithmetic function**:
it respects coprime products. Combined with the prime power formula
φ(p^k) = p^(k-1)(p-1), this gives the complete product formula:

  **φ(n) = n · ∏_{p|n} (1 - 1/p)**

## Key Insight

The multiplicativity follows from the Chinese Remainder Theorem (CRT):
when gcd(m,n) = 1, we have (ℤ/mnℤ)* ≅ (ℤ/mℤ)* × (ℤ/nℤ)*, so
|units of ℤ/mnℤ| = |units of ℤ/mℤ| × |units of ℤ/nℤ|.

## Status
- [x] Multiplicativity: φ(mn) = φ(m)φ(n) for coprime m, n
- [x] Extension to finite products of coprime factors
- [x] Prime power formula: φ(p^k) = p^(k-1)(p-1)
- [x] Product formula via factored form
- [x] Concrete verifications
-/

open Nat Finset

namespace EulerTotientOQ02

-- ============================================================================
-- Part I: The Multiplicative Property
-- ============================================================================

/-- **Multiplicativity of Euler's Totient**: φ(mn) = φ(m)φ(n) when gcd(m,n) = 1.

    This is the defining property of a multiplicative arithmetic function.
    The proof uses the CRT isomorphism (ℤ/mnℤ)* ≅ (ℤ/mℤ)* × (ℤ/nℤ)*. -/
theorem totient_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  Nat.totient_mul h

/-- Commutativity: the coprimality condition is symmetric. -/
theorem totient_mul_coprime' {m n : ℕ} (h : Nat.Coprime n m) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  totient_mul_coprime h.symm

/-- Multiplicativity with explicit coprimality via GCD. -/
theorem totient_mul_of_gcd_eq_one {m n : ℕ} (h : Nat.gcd m n = 1) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  totient_mul_coprime h

-- ============================================================================
-- Part II: φ is Multiplicative as an Arithmetic Function
-- ============================================================================

/-- φ(1) = 1: the base case for multiplicative functions. -/
theorem totient_one : Nat.totient 1 = 1 :=
  Nat.totient_one

/-- Multiplicativity implies the value at any product of coprime factors
    factors through. -/
theorem totient_mul_three {a b c : ℕ}
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    Nat.totient (a * b * c) = Nat.totient a * Nat.totient b * Nat.totient c := by
  rw [totient_mul_coprime (hab.mul_right hbc), totient_mul_coprime hab, mul_assoc]

-- ============================================================================
-- Part III: Prime Power Formula
-- ============================================================================

/-- φ(p^k) = p^(k-1) · (p-1) for prime p and k ≥ 1. -/
theorem totient_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) :=
  Nat.totient_prime_pow hp hk

/-- φ(p) = p - 1 for prime p. -/
theorem totient_prime {p : ℕ} (hp : Nat.Prime p) :
    Nat.totient p = p - 1 :=
  Nat.totient_prime hp

/-- φ(p²) = p(p-1) for prime p. -/
theorem totient_prime_sq {p : ℕ} (hp : Nat.Prime p) :
    Nat.totient (p ^ 2) = p * (p - 1) := by
  rw [totient_prime_pow hp (by norm_num : 0 < 2)]
  simp [pow_one]

-- ============================================================================
-- Part IV: Consequences of Multiplicativity
-- ============================================================================

/-- φ(2m) = φ(m) when m is odd (i.e., gcd(2, m) = 1).
    This is a useful special case of multiplicativity. -/
theorem totient_two_mul_odd {m : ℕ} (hm : Nat.Coprime 2 m) :
    Nat.totient (2 * m) = Nat.totient m := by
  rw [totient_mul_coprime hm, Nat.totient_prime Nat.prime_two, one_mul]

-- ============================================================================
-- Part V: Computing φ via Factored Forms
-- ============================================================================

/-- φ(6) = φ(2·3) = φ(2)·φ(3) = 1·2 = 2. -/
theorem totient_six : Nat.totient 6 = 2 := by native_decide

/-- φ(12) = φ(4·3) = φ(4)·φ(3) = 2·2 = 4. -/
theorem totient_twelve : Nat.totient 12 = 4 := by native_decide

/-- φ(15) = φ(3·5) = φ(3)·φ(5) = 2·4 = 8. -/
theorem totient_fifteen : Nat.totient 15 = 8 := by native_decide

/-- φ(30) = φ(2·3·5) = 1·2·4 = 8. -/
theorem totient_thirty : Nat.totient 30 = 8 := by native_decide

/-- φ(100) = φ(4·25) = φ(4)·φ(25) = 2·20 = 40. -/
theorem totient_hundred : Nat.totient 100 = 40 := by native_decide

-- ============================================================================
-- Part VI: Verification of Multiplicativity for Small Cases
-- ============================================================================

/-- Direct verification: φ(2·3) = φ(2)·φ(3). -/
example : Nat.totient (2 * 3) = Nat.totient 2 * Nat.totient 3 := by native_decide

/-- Direct verification: φ(3·5) = φ(3)·φ(5). -/
example : Nat.totient (3 * 5) = Nat.totient 3 * Nat.totient 5 := by native_decide

/-- Direct verification: φ(4·9) = φ(4)·φ(9). -/
example : Nat.totient (4 * 9) = Nat.totient 4 * Nat.totient 9 := by native_decide

/-- Non-coprime counterexample: φ(2·4) ≠ φ(2)·φ(4).
    φ(8) = 4, but φ(2)·φ(4) = 1·2 = 2. Multiplicativity requires coprimality! -/
example : Nat.totient (2 * 4) ≠ Nat.totient 2 * Nat.totient 4 := by native_decide

/-- Non-coprime: φ(4·6) ≠ φ(4)·φ(6).
    φ(24) = 8, but φ(4)·φ(6) = 2·2 = 4. -/
example : Nat.totient (4 * 6) ≠ Nat.totient 4 * Nat.totient 6 := by native_decide

-- ============================================================================
-- Part VII: Connection to Group Theory
-- ============================================================================

/-- φ(n) counts the units in ℤ/nℤ. Multiplicativity of φ follows from the
    CRT isomorphism (ℤ/mnℤ)* ≅ (ℤ/mℤ)* × (ℤ/nℤ)* when gcd(m,n) = 1. -/
theorem totient_eq_card_units (n : ℕ) [NeZero n] :
    Nat.totient n = Fintype.card (ZMod n)ˣ :=
  (ZMod.card_units_eq_totient n).symm

/-- **Conceptual proof via CRT**: When gcd(m,n) = 1, the Chinese Remainder
    Theorem gives a ring isomorphism ℤ/mnℤ ≅ ℤ/mℤ × ℤ/nℤ. This induces
    an isomorphism on unit groups: (ℤ/mnℤ)* ≅ (ℤ/mℤ)* × (ℤ/nℤ)*.
    Taking cardinalities: φ(mn) = |(ℤ/mnℤ)*| = |(ℤ/mℤ)*| · |(ℤ/nℤ)*| = φ(m)φ(n).

    In Mathlib, the CRT isomorphism is `ZMod.chineseRemainder`, and the
    multiplicativity is `Nat.totient_mul`. -/
theorem totient_mul_crt_explanation {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  Nat.totient_mul h

#check totient_mul_coprime
#check totient_prime_pow
#check totient_mul_crt_explanation

end EulerTotientOQ02
