import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# Law of Quadratic Reciprocity

## What This Proves
The Law of Quadratic Reciprocity, often called Gauss's "golden theorem" of number theory.
For distinct odd primes p and q:

  (p/q)(q/p) = (-1)^((p-1)/2 · (q-1)/2)

where (p/q) is the Legendre symbol, which equals:
- 1 if p is a quadratic residue mod q
- -1 if p is a quadratic nonresidue mod q
- 0 if q divides p

This can be restated: the Legendre symbols (p/q) and (q/p) are equal unless both
p ≡ 3 (mod 4) and q ≡ 3 (mod 4), in which case they are negatives of each other.

We also prove the two supplementary laws:
1. First Supplementary Law: -1 is a square mod p iff p ≡ 1 (mod 4)
2. Second Supplementary Law: 2 is a square mod p iff p ≡ ±1 (mod 8)

## Historical Context
Quadratic reciprocity was conjectured by Euler and Legendre, but first proven by
Carl Friedrich Gauss in 1796 when he was 19 years old. Gauss considered it his
favorite theorem and published eight different proofs throughout his lifetime.
The theorem reveals deep connections between prime numbers and has been
generalized to higher reciprocity laws.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`
  which provides the complete proof. The key theorems are `legendreSym.quadratic_reciprocity`
  and the supplementary laws.
- **Original Contributions:** Pedagogical wrapper theorems with explicit documentation
  explaining the theorem's significance and the various equivalent formulations.
- **Proof Techniques Demonstrated:** Working with Legendre symbols, modular arithmetic,
  and the structure of the multiplicative group (ℤ/pℤ)*.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` : Main theorem
- `legendreSym` : Legendre symbol definition
- `legendreSym.quadratic_reciprocity` : The law of quadratic reciprocity

## Why This Theorem is Important
Quadratic reciprocity is fundamental to:
- Determining which integers are quadratic residues modulo primes
- Cryptographic applications (RSA, primality testing)
- Generalizations to algebraic number fields (Artin reciprocity)
- Understanding the structure of Galois groups

## Wiedijk's 100 Theorems: #7
-/

namespace QuadraticReciprocity

open ZMod

/-! ## The Main Law of Quadratic Reciprocity -/

/-- **The Law of Quadratic Reciprocity (Product Form)**

    For distinct odd primes p and q:
    (q/p) × (p/q) = (-1)^((p-1)/2 × (q-1)/2)

    This is the classic multiplicative form of the law. The exponent
    (p-1)/2 × (q-1)/2 counts how many of the pairs {1,...,(p-1)/2} × {1,...,(q-1)/2}
    have products exceeding pq/2. -/
theorem quadratic_reciprocity_product {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hpq

/-- **The Law of Quadratic Reciprocity (Quotient Form)**

    For distinct odd primes p and q:
    (q/p) = (-1)^((p-1)/2 × (q-1)/2) × (p/q)

    This form shows that knowing (p/q) determines (q/p) up to a sign
    that depends only on the residues of p and q modulo 4. -/
theorem quadratic_reciprocity_quotient {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q :=
  legendreSym.quadratic_reciprocity' hp hq

/-- **Reciprocity for p ≡ 1 (mod 4)**

    If p ≡ 1 (mod 4), then (q/p) = (p/q).

    When p ≡ 1 (mod 4), the sign factor (-1)^((p-1)/2) = 1,
    so the Legendre symbols are equal regardless of q's residue. -/
theorem reciprocity_one_mod_four {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p % 4 = 1) (hq : q ≠ 2) :
    legendreSym q p = legendreSym p q :=
  legendreSym.quadratic_reciprocity_one_mod_four hp hq

/-- **Reciprocity for p ≡ q ≡ 3 (mod 4)**

    If both p ≡ 3 (mod 4) and q ≡ 3 (mod 4), then (q/p) = -(p/q).

    This is the only case where the Legendre symbols differ in sign.
    Equivalently: p is a QR mod q iff q is a QNR mod p. -/
theorem reciprocity_three_mod_four {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = -legendreSym p q :=
  legendreSym.quadratic_reciprocity_three_mod_four hp hq

/-! ## First Supplementary Law: (-1/p) -/

/-- **First Supplementary Law**

    -1 is a quadratic residue mod p iff p ≢ 3 (mod 4).

    Equivalently:
    - (-1/p) = 1 if p ≡ 1 (mod 4)
    - (-1/p) = -1 if p ≡ 3 (mod 4) -/
theorem first_supplementary_law {p : ℕ} [Fact p.Prime] :
    IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 :=
  ZMod.exists_sq_eq_neg_one_iff

/-! ## Second Supplementary Law: (2/p) -/

/-- **Second Supplementary Law**

    2 is a quadratic residue mod p iff p ≡ ±1 (mod 8).

    Equivalently:
    - (2/p) = 1 if p ≡ 1 or 7 (mod 8)
    - (2/p) = -1 if p ≡ 3 or 5 (mod 8) -/
theorem second_supplementary_law {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  ZMod.exists_sq_eq_two_iff hp

/-- **-2 is a square mod p iff p ≡ 1 or 3 (mod 8)**

    Combined first and second supplementary laws. -/
theorem neg_two_is_square_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 :=
  ZMod.exists_sq_eq_neg_two_iff hp

/-! ## Existence of Square Roots Between Primes -/

/-- If p ≡ 1 (mod 4), then q is a square mod p iff p is a square mod q. -/
theorem exists_sq_eq_prime_one_mod_four {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
    IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q) :=
  ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp1 hq1

/-- If p ≡ q ≡ 3 (mod 4), then q is a square mod p iff p is NOT a square mod q. -/
theorem exists_sq_eq_prime_three_mod_four {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) (hpq : p ≠ q) :
    IsSquare (q : ZMod p) ↔ ¬IsSquare (p : ZMod q) :=
  ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp3 hq3 hpq

/-! ## Examples

### Reciprocity Examples

**Example: 3 and 5**
3 and 5 are odd primes with 5 ≡ 1 (mod 4), so by reciprocity_one_mod_four,
(3/5) = (5/3). We have 5 ≡ 2 (mod 3), and 2 is a QNR mod 3, so (5/3) = -1.
Therefore (3/5) = -1, meaning 3 is a QNR mod 5.
Check: squares mod 5 are {0, 1, 4}, and 3 is not among them. ✓

**Example: 3 and 7**
3 and 7 both satisfy p ≡ 3 (mod 4), so by reciprocity_three_mod_four,
(3/7) = -(7/3). We have 7 ≡ 1 (mod 3), and 1 is a QR, so (7/3) = 1.
Therefore (3/7) = -1.
Check: squares mod 7 are {0, 1, 2, 4}, and 3 is not among them. ✓

### First Supplementary Law Examples

**Example: p = 5**
5 ≡ 1 (mod 4), so -1 is a QR mod 5.
Indeed, 2² = 4 ≡ -1 (mod 5). ✓

**Example: p = 7**
7 ≡ 3 (mod 4), so -1 is a QNR mod 7.
Check: squares mod 7 are {0, 1, 2, 4}, and 6 ≡ -1 is not among them. ✓

### Second Supplementary Law Examples

**Example: p = 7**
7 ≡ 7 (mod 8), so 2 is a QR mod 7.
Indeed, 3² = 9 ≡ 2 (mod 7). ✓

**Example: p = 5**
5 ≡ 5 (mod 8), so 2 is a QNR mod 5.
Check: squares mod 5 are {0, 1, 4}, and 2 is not among them. ✓
-/

/-! ## Connection to Euler's Criterion

The Legendre symbol satisfies Euler's criterion:
(a/p) ≡ a^((p-1)/2) (mod p)

This provides a computational method for evaluating the Legendre symbol. -/

/-- Euler's criterion: (a/p) ≡ a^((p-1)/2) (mod p). -/
theorem euler_criterion (p : ℕ) [Fact p.Prime] (a : ℤ) :
    (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) :=
  legendreSym.eq_pow p a

/-! ## The Legendre Symbol is Multiplicative

The Legendre symbol (·/p) is a completely multiplicative function,
meaning (ab/p) = (a/p)(b/p) for all integers a and b. -/

/-- Multiplicativity of the Legendre symbol. -/
theorem legendre_mul (p : ℕ) [Fact p.Prime] (a b : ℤ) :
    legendreSym p (a * b) = legendreSym p a * legendreSym p b :=
  legendreSym.mul p a b

/-! ## Key Theorems Summary -/

#check quadratic_reciprocity_product
#check quadratic_reciprocity_quotient
#check reciprocity_one_mod_four
#check reciprocity_three_mod_four
#check first_supplementary_law
#check second_supplementary_law

end QuadraticReciprocity
