import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic

/-!
# Wilson's Theorem

## What This Proves
Wilson's theorem: A natural number n > 1 is prime if and only if (n-1)! ≡ -1 (mod n).

This beautiful characterization of primes connects factorial arithmetic with
primality. While computationally impractical for primality testing (factorials
grow too fast), it reveals deep structure about prime modular arithmetic.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.NumberTheory.Wilson` which
  provides the complete proof. The key theorems are `ZMod.wilsons_lemma` and
  `Nat.prime_iff_fac_equiv_neg_one`.
- **Original Contributions:** Pedagogical wrapper theorems with explicit
  documentation explaining the proof's connection to group theory.
- **Proof Techniques Demonstrated:** Working with ZMod, factorial congruences,
  and the structure of multiplicative groups.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.NumberTheory.Wilson` : Wilson's theorem and related results
- `ZMod.wilsons_lemma` : (p-1)! ≡ -1 (mod p) for prime p
- `Nat.prime_iff_fac_equiv_neg_one` : The biconditional characterization

## Historical Note
Wilson's theorem was first stated by Ibn al-Haytham (c. 1000 CE), though it
is named after John Wilson who conjectured it in 1770. The first proof was
given by Lagrange in 1771.

## Why This Works
In the multiplicative group (ℤ/pℤ)*, every element except 1 and -1 pairs
with its distinct inverse. The product of all elements is thus the product
of such pairs (each giving 1) times 1 times (-1), yielding -1.

## Wiedijk's 100 Theorems: #51
-/

namespace WilsonsTheorem

/-! ## The Main Theorems -/

/-- **Wilson's Lemma**: For a prime p, (p-1)! ≡ -1 (mod p).

    This is the forward direction of Wilson's theorem.
    The product of all nonzero elements in ℤ/pℤ equals -1. -/
theorem wilsons_lemma (p : ℕ) [_hp : Fact (Nat.Prime p)] :
    (↑(p - 1).factorial : ZMod p) = -1 :=
  ZMod.wilsons_lemma p

/-- **Wilson's Theorem (Full Characterization)**: n > 1 is prime iff (n-1)! ≡ -1 (mod n).

    This beautiful result provides a complete characterization of primality
    in terms of factorial congruence.

    Forward direction (n prime → factorial ≡ -1):
      In (ℤ/pℤ)*, every element pairs with its multiplicative inverse.
      For elements a where a ≠ a⁻¹, the pairs contribute 1 to the product.
      Only 1 and -1 are self-inverse (solutions to x² ≡ 1).
      So (p-1)! = 1 × (-1) × (product of pairs) = -1.

    Backward direction ((n-1)! ≡ -1 → n prime):
      If n = ab with 1 < a, b < n, then a divides (n-1)!.
      If (n-1)! ≡ -1 (mod n), then a would divide (n-1)! + 1.
      Combined: a divides 1, contradiction. So n is prime. -/
theorem wilsons_theorem {n : ℕ} (hn : n ≠ 1) :
    Nat.Prime n ↔ (↑(n - 1).factorial : ZMod n) = -1 :=
  Nat.prime_iff_fac_equiv_neg_one hn

/-- Forward direction: prime implies factorial congruence. -/
theorem prime_implies_factorial_neg_one {p : ℕ} (hp : Nat.Prime p) :
    (↑(p - 1).factorial : ZMod p) = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ZMod.wilsons_lemma p

/-- Backward direction: factorial congruence implies prime (for n ≠ 1). -/
theorem factorial_neg_one_implies_prime {n : ℕ}
    (h : (↑(n - 1).factorial : ZMod n) = -1) (hn : n ≠ 1) :
    Nat.Prime n :=
  Nat.prime_of_fac_equiv_neg_one h hn

/-! ## Product Formulation -/

/-- The product of 1 through p-1 in ℤ/pℤ equals -1.
    This is an alternative formulation using products over intervals. -/
theorem prod_one_to_pred_prime (p : ℕ) [_hp : Fact (Nat.Prime p)] :
    ∏ x ∈ Finset.Ico 1 p, (x : ZMod p) = -1 :=
  ZMod.prod_Ico_one_prime p

/-! ## Corollaries and Applications -/

/-- For p = 2, the theorem gives: 1! = 1 ≡ -1 (mod 2), which checks out
    since -1 ≡ 1 (mod 2). -/
example : (↑(2 - 1).factorial : ZMod 2) = -1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ZMod.wilsons_lemma 2

/-- For p = 5, we have 4! = 24 ≡ -1 ≡ 4 (mod 5). -/
example : (↑(5 - 1).factorial : ZMod 5) = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact ZMod.wilsons_lemma 5

/-- 4 is not prime: 3! = 6 ≡ 2 (mod 4), not ≡ -1 ≡ 3 (mod 4). -/
example : ¬Nat.Prime 4 := by decide

/-! ## Why This is Computationally Impractical

While Wilson's theorem provides a beautiful characterization of primes,
it is not useful for primality testing in practice:

1. **Factorial Growth**: (n-1)! grows super-exponentially. For n = 100,
   we'd need to compute 99!, which has 156 digits.

2. **No Shortcut**: Unlike modular exponentiation (used in Fermat/Miller-Rabin
   tests), there's no known way to compute (n-1)! mod n faster than computing
   the full product.

3. **Better Alternatives**: The Miller-Rabin test runs in O(k log³ n) time
   for k iterations, while computing (n-1)! mod n takes O(n log² n) time.

Wilson's theorem remains valuable for:
- Theoretical insights into prime structure
- Proving properties of primes in formal mathematics
- Understanding the multiplicative group (ℤ/pℤ)*
-/

/-! ## Connection to Group Theory

The proof of Wilson's theorem is essentially a statement about the
multiplicative group (ℤ/pℤ)*:

1. **(ℤ/pℤ)* is cyclic of order p-1**: Every nonzero element mod p is
   invertible, and the group is cyclic (has a generator).

2. **Self-inverse elements**: In any group, x² = 1 iff x = x⁻¹.
   In (ℤ/pℤ)*, this means x² ≡ 1 (mod p).
   The only solutions are x ≡ ±1 (since x² - 1 = (x-1)(x+1) and p is prime).

3. **Pairing argument**: Elements pair as {a, a⁻¹} for a ≠ ±1.
   The product over all pairs is 1.
   The remaining elements 1 and -1 give product 1 × (-1) = -1.

Thus (p-1)! = ∏_{a=1}^{p-1} a = 1 × (-1) × ∏_{pairs} a · a⁻¹ = -1.
-/

#check wilsons_lemma
#check wilsons_theorem
#check prime_implies_factorial_neg_one
#check factorial_neg_one_implies_prime

end WilsonsTheorem
