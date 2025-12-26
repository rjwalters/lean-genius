import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Euler's Generalization of Fermat's Little Theorem

## What This Proves
Euler's Theorem: For any integer a and positive integer n that are coprime (gcd(a, n) = 1),
we have a^φ(n) ≡ 1 (mod n), where φ(n) is Euler's totient function.

This is a generalization of Fermat's Little Theorem, which is the special case when n is prime.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `ZMod.pow_totient` for the main result.
- **Key Insight:** The multiplicative group of units in Z/nZ has order φ(n), so by Lagrange's
  theorem, any unit raised to the φ(n) power equals 1.
- **Proof Techniques Demonstrated:** Modular arithmetic, group theory over ZMod, coercions.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries (Fermat's Little Theorem)
- [x] Pedagogical examples (verification for small primes)
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `ZMod.pow_totient` : Main Euler's theorem for units in ZMod
- `Nat.totient` : Definition of Euler's totient function
- `Nat.totient_prime` : φ(p) = p - 1 for prime p
- `ZMod.unitOfCoprime` : Construct a unit from coprimality

## Historical Note
Euler published this generalization in 1763. It extends Fermat's Little Theorem (1640)
from prime moduli to arbitrary positive integers. The theorem is fundamental to
RSA cryptography, primality testing, and modular arithmetic applications.

This is #10 on Wiedijk's list of 100 theorems.
-/

namespace EulerTotient

/-! ## The Main Theorem: Euler's Theorem

If a is a unit in Z/nZ (equivalently, gcd(a, n) = 1), then a^φ(n) = 1.

The proof follows from the fact that the multiplicative group (Z/nZ)* has order φ(n),
so by Lagrange's theorem any element raised to the group order is the identity. -/

/-- **Euler's Generalization of Fermat's Little Theorem (Wiedijk #10)**

For n > 0 and a coprime to n (i.e., a is a unit in Z/nZ), we have a^φ(n) = 1.

This is the most natural formulation using ZMod units. -/
theorem euler_totient (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    a ^ Nat.totient n = 1 :=
  ZMod.pow_totient a

/-! ## Fermat's Little Theorem as a Corollary

Fermat's Little Theorem is the special case of Euler's theorem when n = p is prime.
Since φ(p) = p - 1 for prime p, we get a^(p-1) ≡ 1 (mod p). -/

/-- **Fermat's Little Theorem**

For prime p and a coprime to p (a unit in Z/pZ), we have a^(p-1) = 1.

This follows from Euler's theorem since φ(p) = p - 1 for prime p. -/
theorem fermat_little_theorem (p : ℕ) [Fact (Nat.Prime p)] (a : (ZMod p)ˣ) :
    a ^ (p - 1) = 1 := by
  have h : Nat.totient p = p - 1 := Nat.totient_prime (Fact.out : Nat.Prime p)
  rw [← h]
  exact euler_totient p a

/-- Fermat's Little Theorem: alternative statement with the full power.

For prime p, a^p ≡ a (mod p) for any a. This holds even when a is not coprime to p
(when p divides a, both sides are 0). -/
theorem fermat_little_theorem_full (p : ℕ) [Fact (Nat.Prime p)] (a : ZMod p) :
    a ^ p = a :=
  ZMod.pow_card a

/-! ## Examples and Verification

Let's verify Euler's theorem for small cases. -/

/-- φ(1) = 1, so a^1 = a = 1 in Z/1Z (the trivial ring) -/
example : Nat.totient 1 = 1 := rfl

/-- φ(2) = 1, so a^1 = 1 for the unique unit 1 in Z/2Z -/
example : Nat.totient 2 = 1 := rfl

/-- φ(3) = 2, since 1 and 2 are coprime to 3 -/
example : Nat.totient 3 = 2 := rfl

/-- φ(4) = 2, since 1 and 3 are coprime to 4 -/
example : Nat.totient 4 = 2 := rfl

/-- φ(5) = 4, since 1, 2, 3, 4 are all coprime to 5 -/
example : Nat.totient 5 = 4 := rfl

/-- φ(6) = 2, since only 1 and 5 are coprime to 6 -/
example : Nat.totient 6 = 2 := rfl

/-- Verify 2^φ(5) = 2^4 = 16 ≡ 1 (mod 5) -/
example : (2 : ZMod 5) ^ Nat.totient 5 = 1 := by native_decide

/-- Verify 3^φ(7) = 3^6 ≡ 1 (mod 7) -/
example : (3 : ZMod 7) ^ Nat.totient 7 = 1 := by native_decide

/-- Verify Fermat's Little Theorem: 2^6 ≡ 1 (mod 7) -/
example : (2 : ZMod 7) ^ 6 = 1 := by native_decide

/-- Non-coprime case: 2^φ(4) = 2^2 = 4 ≡ 0 (mod 4), NOT 1
    (Euler's theorem requires coprimality) -/
example : (2 : ZMod 4) ^ Nat.totient 4 ≠ 1 := by native_decide

/-! ## Properties of Euler's Totient Function

Some useful properties that help understand the theorem. -/

/-- The totient of a prime is p - 1 -/
theorem totient_prime (p : ℕ) (hp : Nat.Prime p) : Nat.totient p = p - 1 :=
  Nat.totient_prime hp

/-- The totient of a prime power is p^(k-1) * (p - 1) -/
theorem totient_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) :=
  Nat.totient_prime_pow hp hk

#check euler_totient
#check fermat_little_theorem
#check fermat_little_theorem_full

end EulerTotient
