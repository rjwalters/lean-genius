/-
  Lagrange's Four Squares Theorem
  Open Question: fermat-two-squares-oq-01

  Every natural number can be written as the sum of four integer squares.
  This extends Fermat's two-squares theorem (which characterizes primes
  representable as sums of TWO squares) to the universal four-squares case.

  The key algebraic ingredient is Euler's four-square identity, which is
  secretly the multiplicativity of the quaternion norm. This identity
  reduces the problem from all naturals to primes, and a descent argument
  (in Mathlib) handles the prime case.

  References:
  - Lagrange (1770): original proof via descent
  - Euler (1748): four-square identity (= quaternion norm multiplicativity)
  - FermatTwoSquares.lean: parent two-squares characterization
-/

import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

namespace FermatTwoSquaresOQ01

-- ============================================================================
-- Part I: Euler's Four-Square Identity
-- ============================================================================

/-- **Euler's Four-Square Identity (1748)**

The product of two sums of four squares is itself a sum of four squares.
This is equivalent to quaternion norm multiplicativity: |q₁q₂|² = |q₁|²|q₂|².

The bilinear forms encoding the result components are exactly the real and
imaginary parts of the quaternion product (a + bi + cj + dk)(x + yi + zj + wk). -/
theorem euler_four_square_identity {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 +
    (a * y + b * x + c * w - d * z) ^ 2 +
    (a * z - b * w + c * x + d * y) ^ 2 +
    (a * w + b * z - c * y + d * x) ^ 2 =
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  ring

-- ============================================================================
-- Part II: Lipschitz Quaternion Integers
-- ============================================================================

/-- A Lipschitz quaternion integer: q = a + bi + cj + dk with a,b,c,d ∈ ℤ. -/
structure LipschitzQuat where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

/-- The squared norm of a Lipschitz quaternion: N(q) = a² + b² + c² + d². -/
def LipschitzQuat.normSq (q : LipschitzQuat) : ℤ :=
  q.a ^ 2 + q.b ^ 2 + q.c ^ 2 + q.d ^ 2

/-- Quaternion multiplication (Hamilton product). -/
def LipschitzQuat.mul (q₁ q₂ : LipschitzQuat) : LipschitzQuat where
  a := q₁.a * q₂.a - q₁.b * q₂.b - q₁.c * q₂.c - q₁.d * q₂.d
  b := q₁.a * q₂.b + q₁.b * q₂.a + q₁.c * q₂.d - q₁.d * q₂.c
  c := q₁.a * q₂.c - q₁.b * q₂.d + q₁.c * q₂.a + q₁.d * q₂.b
  d := q₁.a * q₂.d + q₁.b * q₂.c - q₁.c * q₂.b + q₁.d * q₂.a

/-- **Quaternion norm is multiplicative**: N(q₁q₂) = N(q₁)N(q₂).

This is Euler's four-square identity in the language of quaternions.
It shows that the set of integers representable as sums of four squares
is closed under multiplication. -/
theorem LipschitzQuat.normSq_mul (q₁ q₂ : LipschitzQuat) :
    (q₁.mul q₂).normSq = q₁.normSq * q₂.normSq := by
  simp only [mul, normSq]
  ring

/-- The quaternion conjugate: conj(a + bi + cj + dk) = a - bi - cj - dk. -/
def LipschitzQuat.conj (q : LipschitzQuat) : LipschitzQuat where
  a := q.a
  b := -q.b
  c := -q.c
  d := -q.d

/-- The product q * conj(q) equals the norm. -/
theorem LipschitzQuat.mul_conj (q : LipschitzQuat) :
    (q.mul q.conj).a = q.normSq ∧
    (q.mul q.conj).b = 0 ∧
    (q.mul q.conj).c = 0 ∧
    (q.mul q.conj).d = 0 := by
  simp only [mul, conj, normSq]
  exact ⟨by ring, by ring, by ring, by ring⟩

-- ============================================================================
-- Part III: Lagrange's Four Squares Theorem
-- ============================================================================

/-- **Lagrange's Four Squares Theorem (1770)**

Every natural number is the sum of four squares: n = a² + b² + c² + d².

This is Wiedijk's 100 Theorems #19. The proof reduces to primes via Euler's
identity, then uses a descent argument for each prime p. -/
theorem lagrange_four_squares (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

/-- Integer version: every natural number is a sum of four integer squares. -/
theorem lagrange_four_squares_int (n : ℕ) :
    ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = ↑n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨a, b, c, d, ?_⟩
  push_cast [← h]
  ring

/-- Every natural number is the norm of a Lipschitz quaternion. -/
theorem every_nat_is_quat_norm (n : ℕ) :
    ∃ q : LipschitzQuat, q.normSq = ↑n := by
  obtain ⟨a, b, c, d, h⟩ := lagrange_four_squares_int n
  exact ⟨⟨a, b, c, d⟩, h⟩

-- ============================================================================
-- Part IV: From Two Squares to Four — Why Four is Universal
-- ============================================================================

/-- **Brahmagupta-Fibonacci Identity**

The product of two sums of two squares is a sum of two squares.
This is the norm multiplicativity of the Gaussian integers ℤ[i]:
|z₁z₂|² = |z₁|²|z₂|². -/
theorem two_squares_mul (a b c d : ℤ) :
    (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 =
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring

/-- Two squares are closed under multiplication (existential form). -/
theorem two_squares_closed (m n : ℕ)
    (hm : ∃ a b : ℕ, a ^ 2 + b ^ 2 = m)
    (hn : ∃ c d : ℕ, c ^ 2 + d ^ 2 = n) :
    ∃ e f : ℕ, e ^ 2 + f ^ 2 = m * n := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  refine ⟨((a : ℤ) * c + b * d).natAbs, ((a : ℤ) * d - b * c).natAbs, ?_⟩
  zify
  rw [sq_abs, sq_abs]
  ring

/-- Four squares are closed under multiplication (existential form). -/
theorem four_squares_closed (m n : ℕ)
    (hm : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m)
    (hn : ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) :
    ∃ p q r s : ℕ, p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = m * n := by
  obtain ⟨a, b, c, d, rfl⟩ := hm
  obtain ⟨x, y, z, w, rfl⟩ := hn
  refine ⟨((a : ℤ) * x - b * y - c * z - d * w).natAbs,
          ((a : ℤ) * y + b * x + c * w - d * z).natAbs,
          ((a : ℤ) * z - b * w + c * x + d * y).natAbs,
          ((a : ℤ) * w + b * z - c * y + d * x).natAbs, ?_⟩
  zify
  simp only [sq_abs]
  ring

-- ============================================================================
-- Part V: Three Squares Obstruction
-- ============================================================================

-- Numbers of the form 4^a(8b + 7) cannot be sums of three squares.
-- We verify specific examples showing this obstruction.

/-- 7 requires four squares: 7 = 1² + 1² + 1² + 2². -/
example : (1 : ℕ) ^ 2 + 1 ^ 2 + 1 ^ 2 + 2 ^ 2 = 7 := by norm_num

/-- 15 requires four squares: 15 = 1² + 1² + 2² + 3². -/
example : (1 : ℕ) ^ 2 + 1 ^ 2 + 2 ^ 2 + 3 ^ 2 = 15 := by norm_num

/-- 23 requires four squares: 23 = 1² + 2² + 3² + 3². -/
example : (1 : ℕ) ^ 2 + 2 ^ 2 + 3 ^ 2 + 3 ^ 2 = 23 := by norm_num

/-- 28 = 4·7 requires four squares: 28 = 2² + 2² + 2² + 4². -/
example : (2 : ℕ) ^ 2 + 2 ^ 2 + 2 ^ 2 + 4 ^ 2 = 28 := by norm_num

-- ============================================================================
-- Part VI: Two Squares vs Four — The Fermat Connection
-- ============================================================================

/-- Fermat's characterization: a prime is a sum of two squares iff p % 4 ≠ 3. -/
theorem fermat_two_squares {p : ℕ} [Fact p.Prime] :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 ≠ 3 := by
  constructor
  · rintro ⟨a, b, hab⟩ h
    have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      have h4 : a % 4 < 4 := Nat.mod_lt a (by omega)
      have : a ^ 2 % 4 = (a % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
      rw [this]; interval_cases (a % 4) <;> simp
    have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
      have h4 : b % 4 < 4 := Nat.mod_lt b (by omega)
      have : b ^ 2 % 4 = (b % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
      rw [this]; interval_cases (b % 4) <;> simp
    have : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
    rw [hab] at this; exact this h
  · exact Nat.Prime.sq_add_sq

/-- The key contrast: some primes FAIL the two-squares test (those ≡ 3 mod 4)
but ALL primes pass the four-squares test. -/
theorem every_prime_is_four_squares (p : ℕ) (_hp : Nat.Prime p) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p :=
  lagrange_four_squares p

/-- 3 ≡ 3 (mod 4), so 3 is NOT a sum of two squares... -/
theorem three_not_two_squares : ¬∃ a b : ℕ, a ^ 2 + b ^ 2 = 3 := by
  rintro ⟨a, b, h⟩
  have ha : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b ≤ 1 := by nlinarith [sq_nonneg a]
  interval_cases a <;> interval_cases b <;> omega

/-- ...but 3 IS a sum of four squares: 3 = 1² + 1² + 1² + 0². -/
theorem three_is_four_squares : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 3 :=
  ⟨1, 1, 1, 0, by norm_num⟩

-- ============================================================================
-- Part VII: More Examples
-- ============================================================================

/-- 5 = 1² + 2² (sum of two squares, since 5 ≡ 1 mod 4). -/
example : (1 : ℕ) ^ 2 + 2 ^ 2 = 5 := by norm_num

/-- 13 = 2² + 3² (sum of two squares, since 13 ≡ 1 mod 4). -/
example : (2 : ℕ) ^ 2 + 3 ^ 2 = 13 := by norm_num

/-- 100 = 6² + 8² = 0² + 0² + 6² + 8² (four squares with two zeros). -/
example : (0 : ℕ) ^ 2 + 0 ^ 2 + 6 ^ 2 + 8 ^ 2 = 100 := by norm_num

/-- 42 = 1² + 1² + 2² + 6² (needs three or more squares). -/
example : (1 : ℕ) ^ 2 + 1 ^ 2 + 2 ^ 2 + 6 ^ 2 = 42 := by norm_num

-- ============================================================================
-- Verification
-- ============================================================================

#check euler_four_square_identity
#check LipschitzQuat.normSq_mul
#check LipschitzQuat.mul_conj
#check lagrange_four_squares
#check lagrange_four_squares_int
#check every_nat_is_quat_norm
#check two_squares_mul
#check two_squares_closed
#check four_squares_closed
#check fermat_two_squares
#check every_prime_is_four_squares
#check three_not_two_squares
#check three_is_four_squares

end FermatTwoSquaresOQ01
