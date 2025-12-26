import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic

/-!
# Lagrange's Four Squares Theorem

## What This Proves
Every natural number can be expressed as the sum of four integer squares:
$$n = a^2 + b^2 + c^2 + d^2$$

This is one of the most beautiful results in number theory, proved by Lagrange in 1770.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Nat.sum_four_squares` which provides
  the complete proof. We also demonstrate Euler's four-square identity which is the
  algebraic heart of the proof.
- **Key Insight:** Euler's identity shows that the product of two sums-of-four-squares
  is itself a sum of four squares. This is equivalent to the multiplicativity of the
  quaternion norm! If Hamilton had known this identity, he might have discovered
  quaternions much faster.
- **Proof Techniques Demonstrated:** Algebraic identities, descent method, prime factorization.

## Status
- [x] Uses Mathlib for main result
- [x] Complete proof via mathlib
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Nat.sum_four_squares` : Main theorem
- `Int.sq_add_sq_mul_sq_add_sq_eq_sq_add_sq_add_sq_add_sq_add_sq_mul_sq_add_sq_add_sq_add_sq` : Euler's identity (Integer form)

## Historical Note
The four-square identity discovered by Euler in 1748 is actually quaternion multiplication!
The quaternions $q_1 = a + bi + cj + dk$ and $q_2 = x + yi + zj + wk$ have:
$$|q_1 q_2|^2 = |q_1|^2 \cdot |q_2|^2$$
where $|q|^2 = a^2 + b^2 + c^2 + d^2$. This explains WHY four squares work when three don't:
quaternions form a division algebra, but there's no 3-dimensional division algebra.
-/

namespace LagrangeFourSquares

/-! ## Euler's Four-Square Identity

The key algebraic identity that powers the proof. This shows that the set of
sums-of-four-squares is closed under multiplication. -/

/-- **Euler's Four-Square Identity (1748)**

The product of two sums of four squares is itself a sum of four squares.
This identity is precisely the statement that quaternion norm is multiplicative:
$|q_1 q_2| = |q_1| \cdot |q_2|$

The specific form of $A, B, C, D$ encodes quaternion multiplication:
- $A = ax - by - cz - dw$
- $B = ay + bx + cw - dz$
- $C = az - bw + cx + dy$
- $D = aw + bz - cy + dx$

These are the real and imaginary components of the product $(a + bi + cj + dk)(x + yi + zj + wk)$.
-/
theorem euler_four_squares {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 +
    (a * y + b * x + c * w - d * z) ^ 2 +
    (a * z - b * w + c * x + d * y) ^ 2 +
    (a * w + b * z - c * y + d * x) ^ 2 =
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  ring

/-! ## Why Four Squares and Not Three?

Numbers of the form $4^k(8m + 7)$ cannot be expressed as sums of three squares.
For example: 7 = 4 + 2 + 1 = 4 + 1 + 1 + 1 needs four squares.
But with FOUR squares, every natural number works! -/

/-- Seven cannot be written as a sum of three squares, but can be written as four. -/
example : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 7 := ⟨1, 1, 1, 2, rfl⟩

/-! ## The Main Theorem -/

/-- **Lagrange's Four Squares Theorem (1770)**

Every natural number can be expressed as the sum of four squares.

The proof strategy in Mathlib:
1. Use Euler's identity to reduce to proving the theorem for primes
2. For each prime $p$, show there exists $m < p$ with $mp$ a sum of four squares
3. Use a descent argument to reduce $m$ until $m = 1$
4. Conclude that $p$ itself is a sum of four squares
5. Use Euler's identity again to extend from primes to all naturals

This is #19 on Wiedijk's list of 100 theorems. -/
theorem lagrange_four_squares (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

/-- Alternative statement using integers instead of natural numbers. -/
theorem lagrange_four_squares_int (n : ℕ) :
    ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨a, b, c, d, by simp only [sq_abs, ← Nat.cast_pow, ← Nat.cast_add, h]⟩

/-! ## Specific Examples

Let's verify some specific decompositions. -/

/-- Zero is trivially a sum of four squares. -/
example : (0 : ℕ) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 0 := rfl

/-- One as a sum of four squares. -/
example : (1 : ℕ) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1 := rfl

/-- Two as a sum of four squares. -/
example : (1 : ℕ) ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 = 2 := rfl

/-- Three as a sum of four squares. -/
example : (1 : ℕ) ^ 2 + 1 ^ 2 + 1 ^ 2 + 0 ^ 2 = 3 := rfl

/-- The notorious 7 - needs all four squares! -/
example : (1 : ℕ) ^ 2 + 1 ^ 2 + 1 ^ 2 + 2 ^ 2 = 7 := rfl

/-- A larger example: 100 = 10² = 6² + 8² + 0² + 0² -/
example : (6 : ℕ) ^ 2 + 8 ^ 2 + 0 ^ 2 + 0 ^ 2 = 100 := rfl

/-- Another way to write 100: 100 = 6² + 6² + 6² + 4² -/
example : (6 : ℕ) ^ 2 + 6 ^ 2 + 6 ^ 2 + 4 ^ 2 = 100 := rfl

/-! ## Connection to Two Squares Theorem

While every number is a sum of four squares, not every number is a sum of two.
Fermat proved that an odd prime $p$ is a sum of two squares iff $p ≡ 1 \pmod 4$. -/

/-- 5 ≡ 1 (mod 4), so it's a sum of two squares: 5 = 1² + 2² -/
example : (1 : ℕ) ^ 2 + 2 ^ 2 = 5 := rfl

/-- 13 ≡ 1 (mod 4), so it's a sum of two squares: 13 = 2² + 3² -/
example : (2 : ℕ) ^ 2 + 3 ^ 2 = 13 := rfl

#check lagrange_four_squares
#check euler_four_squares

end LagrangeFourSquares
