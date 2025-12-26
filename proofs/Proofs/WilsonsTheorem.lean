import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-!
# Wilson's Theorem

## What This Proves
Wilson's Theorem: A natural number n > 1 is prime if and only if (n-1)! ≡ -1 (mod n).

This provides a beautiful characterization of prime numbers through modular arithmetic
of factorials. While computationally inefficient for primality testing, it offers
deep theoretical insight into the structure of primes.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `ZMod.wilsons_lemma` for the forward
  direction and `Nat.prime_of_fac_equiv_neg_one` for the reverse.
- **Key Insight:** In the forward direction, we pair each element with its multiplicative
  inverse mod p. Only 1 and p-1 are self-inverse, so the product of all others is 1,
  leaving (p-1)! ≡ (p-1) ≡ -1 (mod p).
- **Proof Techniques Demonstrated:** Modular arithmetic, group theory over ZMod, iff proofs.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `ZMod.wilsons_lemma` : Forward direction (prime → (p-1)! ≡ -1)
- `Nat.prime_of_fac_equiv_neg_one` : Reverse direction ((n-1)! ≡ -1 → prime)
- `Nat.prime_iff_fac_equiv_neg_one` : Complete iff statement

## Historical Note
Wilson's Theorem was first stated by Ibn al-Haytham (c. 1000 CE) and rediscovered
by John Wilson in 1770. Lagrange provided the first published proof in 1773.

This is #51 on Wiedijk's list of 100 theorems.
-/

namespace WilsonsTheorem

/-! ## The Forward Direction

If p is prime, then (p-1)! ≡ -1 (mod p).

The proof works by observing that in Z/pZ (the integers mod p):
- Every nonzero element has a unique multiplicative inverse
- 1 and p-1 are the only elements equal to their own inverse
- All other elements pair up with distinct inverses
- The product of paired elements is 1, leaving only 1 · (p-1) = p-1 ≡ -1 -/

/-- **Wilson's Theorem (Forward Direction)**

If p is prime, then (p-1)! ≡ -1 (mod p).

This is the classical statement using ZMod. -/
theorem prime_implies_factorial_eq_neg_one (p : ℕ) [Fact (Nat.Prime p)] :
    ((p - 1).factorial : ZMod p) = -1 :=
  ZMod.wilsons_lemma p

/-! ## The Reverse Direction

If (n-1)! ≡ -1 (mod n) for n ≠ 1, then n is prime.

The proof works by contraposition: if n is composite with factor d where 1 < d < n,
then d divides (n-1)!, so d divides both (n-1)! and n. If (n-1)! ≡ -1 (mod n),
then n divides (n-1)! + 1, but d divides (n-1)!, so d cannot divide 1.
This contradicts d > 1. -/

/-- **Wilson's Theorem (Reverse Direction)**

If (n-1)! ≡ -1 (mod n) for n ≠ 1, then n is prime.

This completes the characterization: Wilson's condition is sufficient for primality. -/
theorem factorial_eq_neg_one_implies_prime {n : ℕ} (hn : n ≠ 1)
    (h : ((n - 1).factorial : ZMod n) = -1) : Nat.Prime n :=
  Nat.prime_of_fac_equiv_neg_one h hn

/-! ## The Main Theorem: Wilson's Theorem as an Iff

This combines both directions into a single biconditional statement. -/

/-- **Wilson's Theorem (Complete Statement)**

A natural number n ≠ 1 is prime if and only if (n-1)! ≡ -1 (mod n).

This elegant characterization of primes was known to Ibn al-Haytham around 1000 CE
and was proved by Lagrange in 1773. -/
theorem wilsons_theorem {n : ℕ} (hn : n ≠ 1) :
    Nat.Prime n ↔ ((n - 1).factorial : ZMod n) = -1 :=
  Nat.prime_iff_fac_equiv_neg_one hn

/-! ## Examples and Verification

Let's verify Wilson's theorem for small primes. -/

/-- Wilson's theorem for 2: (2-1)! = 1 ≡ -1 (mod 2) -/
example : ((2 - 1).factorial : ZMod 2) = -1 := by native_decide

/-- Wilson's theorem for 3: (3-1)! = 2 ≡ -1 (mod 3) -/
example : ((3 - 1).factorial : ZMod 3) = -1 := by native_decide

/-- Wilson's theorem for 5: (5-1)! = 24 ≡ -1 (mod 5) -/
example : ((5 - 1).factorial : ZMod 5) = -1 := by native_decide

/-- Wilson's theorem for 7: (7-1)! = 720 ≡ -1 (mod 7) -/
example : ((7 - 1).factorial : ZMod 7) = -1 := by native_decide

/-- Non-prime 4 fails Wilson's test: (4-1)! = 6 ≡ 2 (mod 4), not -1 -/
example : ((4 - 1).factorial : ZMod 4) ≠ -1 := by native_decide

/-- Non-prime 6 fails Wilson's test: (6-1)! = 120 ≡ 0 (mod 6), not -1 -/
example : ((6 - 1).factorial : ZMod 6) ≠ -1 := by native_decide

/-! ## Corollaries -/

/-- For any prime p, we have p divides (p-1)! + 1.

This is just Wilson's theorem restated in terms of divisibility. -/
theorem prime_dvd_factorial_succ {p : ℕ} (hp : Nat.Prime p) : p ∣ (p - 1).factorial + 1 := by
  have h : ((p - 1).factorial : ZMod p) = -1 := @ZMod.wilsons_lemma p ⟨hp⟩
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_add, Nat.cast_one, h]
  ring

#check wilsons_theorem
#check prime_implies_factorial_eq_neg_one
#check factorial_eq_neg_one_implies_prime

end WilsonsTheorem
