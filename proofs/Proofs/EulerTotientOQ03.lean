import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# Structural Properties of Euler's Totient

## What This Proves

A collection of structural results about Euler's totient function:

1. **Parity**: φ(n) is even for all n ≥ 3; φ(n) is odd iff n ∈ {1, 2}
2. **Prime characterization**: φ(n) = n − 1 iff n is prime
3. **Divisibility**: a | b ⟹ φ(a) | φ(b)
4. **Super-multiplicativity**: φ(a) · φ(b) ≤ φ(a · b)
5. **Product formula**: φ(n) = n · ∏_{p|n} (1 − 1/p) (over ℚ)
6. **GCD–Totient identity**: φ(gcd(a,b)) · φ(ab) = φ(a) · φ(b) · gcd(a,b)

## Key Insight

The parity result (φ(n) is even for n ≥ 3) follows from the structure of
(ℤ/nℤ)*: the map a ↦ −a = n−a is an involution with no fixed points
when n > 2, so the group has even order.

The GCD–totient identity unifies multiplicativity (coprime case: gcd = 1)
and divisibility (one factor divides the other) into a single statement.

## Approach

Most results wrap the corresponding Mathlib lemmas, but the organization
reveals how these properties interconnect — from local parity through
divisibility to the global product formula.
-/

open Nat Finset

namespace EulerTotientOQ03

-- ============================================================================
-- Part I: Parity of Totient Values
-- ============================================================================

/-- **φ(n) is even for n ≥ 3.**

    In (ℤ/nℤ)*, the map a ↦ −a is a fixed-point-free involution
    when n > 2, so |(ℤ/nℤ)*| = φ(n) is even. -/
theorem totient_even {n : ℕ} (hn : 2 < n) : Even (Nat.totient n) :=
  Nat.totient_even hn

/-- φ(n) is odd precisely when n ∈ {1, 2}. -/
theorem totient_odd_iff {n : ℕ} : Odd (Nat.totient n) ↔ n = 1 ∨ n = 2 :=
  Nat.odd_totient_iff

/-- φ(n) = 1 iff n ∈ {1, 2}. Combining parity with positivity. -/
theorem totient_eq_one_iff {n : ℕ} : Nat.totient n = 1 ↔ n = 1 ∨ n = 2 :=
  Nat.totient_eq_one_iff

-- ============================================================================
-- Part II: The Prime Characterization
-- ============================================================================

/-- **φ(p) = p − 1 iff p is prime** (for p > 0).

    The "only if" direction is key: if every element of {1,...,n−1}
    is coprime to n, then n has no proper divisors, i.e., n is prime. -/
theorem totient_eq_sub_one_iff_prime {p : ℕ} (hp : 0 < p) :
    Nat.totient p = p - 1 ↔ Nat.Prime p :=
  Nat.totient_eq_iff_prime hp

/-- φ(p) = p − 1 for any prime p. -/
theorem totient_prime {p : ℕ} (hp : Nat.Prime p) :
    Nat.totient p = p - 1 :=
  Nat.totient_prime hp

/-- φ(n) < n for all n > 1. (The element 0 is never coprime to n.) -/
theorem totient_lt {n : ℕ} (hn : 1 < n) : Nat.totient n < n :=
  Nat.totient_lt n hn

/-- φ(n) ≤ n always. -/
theorem totient_le (n : ℕ) : Nat.totient n ≤ n :=
  Nat.totient_le n

/-- φ(n) > 0 iff n > 0. -/
theorem totient_pos {n : ℕ} (hn : 0 < n) : 0 < Nat.totient n :=
  Nat.totient_pos.mpr hn

-- ============================================================================
-- Part III: Divisibility Properties
-- ============================================================================

/-- **If a divides b then φ(a) divides φ(b).**

    This follows from the surjection (ℤ/bℤ)* → (ℤ/aℤ)* induced by
    the canonical map ℤ/bℤ → ℤ/aℤ (when a | b), and Lagrange's theorem. -/
theorem totient_dvd_of_dvd {a b : ℕ} (h : a ∣ b) :
    Nat.totient a ∣ Nat.totient b :=
  Nat.totient_dvd_of_dvd h

/-- **Super-multiplicativity**: φ(a) · φ(b) ≤ φ(a · b).

    Equality holds iff gcd(a, b) = 1 (the multiplicativity case from OQ-02).
    Strict inequality can occur, e.g., φ(2) · φ(4) = 2 < 4 = φ(8). -/
theorem totient_super_multiplicative (a b : ℕ) :
    Nat.totient a * Nat.totient b ≤ Nat.totient (a * b) :=
  Nat.totient_super_multiplicative a b

/-- The exact ratio: φ(gcd(a,b)) governs the gap between
    φ(a)·φ(b) and φ(ab). See Part V for the full identity. -/
theorem totient_mul_of_prime_dvd {p n : ℕ} (hp : Nat.Prime p) (h : p ∣ n) :
    Nat.totient (p * n) = p * Nat.totient n :=
  Nat.totient_mul_of_prime_of_dvd hp h

theorem totient_mul_of_prime_not_dvd {p n : ℕ} (hp : Nat.Prime p) (h : ¬p ∣ n) :
    Nat.totient (p * n) = (p - 1) * Nat.totient n :=
  Nat.totient_mul_of_prime_of_not_dvd hp h

-- ============================================================================
-- Part IV: Euler's Product Formula
-- ============================================================================

/-- **Euler's Product Formula** (rational form):
    φ(n) = n · ∏_{p | n} (1 − 1/p)

    This is the most elegant expression of the totient function,
    connecting it to the prime factorization of n. -/
theorem totient_product_formula (n : ℕ) :
    (Nat.totient n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
  Nat.totient_eq_mul_prod_factors n

/-- Product formula (natural number form): uses the factorization directly. -/
theorem totient_factorization_formula {n : ℕ} (hn : n ≠ 0) :
    Nat.totient n = n.factorization.prod (fun p k => p ^ (k - 1) * (p - 1)) :=
  Nat.totient_eq_prod_factorization hn

/-- Division form: φ(n) = (n / ∏ p) · ∏ (p − 1) where p ranges over
    prime factors. -/
theorem totient_div_form (n : ℕ) :
    Nat.totient n = (n / ∏ p ∈ n.primeFactors, p) *
      ∏ p ∈ n.primeFactors, (p - 1) :=
  Nat.totient_eq_div_primeFactors_mul n

-- ============================================================================
-- Part V: The GCD–Totient Identity
-- ============================================================================

/-- **The GCD–Totient Identity**:
    φ(gcd(a,b)) · φ(ab) = φ(a) · φ(b) · gcd(a,b)

    This beautiful identity unifies several facts:
    - When gcd(a,b) = 1: reduces to multiplicativity φ(ab) = φ(a)φ(b)
    - When a | b: the identity relates φ(a), φ(b), and φ(ab) = φ(a)·φ(b/a)·a

    It captures how the "overlap" in (ℤ/aℤ)* × (ℤ/bℤ)* maps onto (ℤ/abℤ)*
    when a and b share common factors. -/
theorem totient_gcd_mul (a b : ℕ) :
    Nat.totient (a.gcd b) * Nat.totient (a * b) =
      Nat.totient a * Nat.totient b * a.gcd b :=
  Nat.totient_gcd_mul_totient_mul a b

-- ============================================================================
-- Part VI: Concrete Verifications
-- ============================================================================

/-- Parity check: φ(3) = 2 is even. -/
example : Even (Nat.totient 3) := ⟨1, by native_decide⟩

/-- Parity check: φ(4) = 2 is even. -/
example : Even (Nat.totient 4) := ⟨1, by native_decide⟩

/-- Parity check: φ(12) = 4 is even. -/
example : Even (Nat.totient 12) := ⟨2, by native_decide⟩

/-- Odd totient: φ(1) = 1. -/
example : Nat.totient 1 = 1 := rfl

/-- Odd totient: φ(2) = 1. -/
example : Nat.totient 2 = 1 := rfl

/-- Prime characterization: φ(7) = 6 = 7 − 1. -/
example : Nat.totient 7 = 6 := by native_decide

/-- Non-prime: φ(9) = 6 ≠ 8 = 9 − 1. -/
example : Nat.totient 9 ≠ 8 := by native_decide

/-- Super-multiplicativity: φ(2)·φ(4) = 1·2 = 2 < 4 = φ(8). -/
example : Nat.totient 2 * Nat.totient 4 < Nat.totient (2 * 4) := by native_decide

/-- Divisibility: 4 | 12 implies φ(4) | φ(12), i.e., 2 | 4. -/
example : Nat.totient 4 ∣ Nat.totient 12 := ⟨2, by native_decide⟩

/-- GCD identity: φ(gcd(6,10))·φ(60) = φ(6)·φ(10)·gcd(6,10).
    gcd(6,10) = 2, φ(2) = 1, φ(60) = 16, φ(6) = 2, φ(10) = 4.
    Check: 1 · 16 = 2 · 4 · 2 = 16. ✓ -/
example : Nat.totient (Nat.gcd 6 10) * Nat.totient (6 * 10) =
    Nat.totient 6 * Nat.totient 10 * Nat.gcd 6 10 := by native_decide

/-- Product formula check: φ(30) = 8 = 30 · (1-1/2)(1-1/3)(1-1/5)
    = 30 · (1/2)(2/3)(4/5) = 30 · 8/30 = 8. -/
example : Nat.totient 30 = 8 := by native_decide

#check totient_even
#check totient_eq_sub_one_iff_prime
#check totient_dvd_of_dvd
#check totient_super_multiplicative
#check totient_product_formula
#check totient_gcd_mul

end EulerTotientOQ03
