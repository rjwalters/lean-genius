import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-
# Fermat's Two-Square Theorem for Primes (pythagorean-triples-oq-04)

Pythagorean triples a² + b² = c² are the integer points on the unit circle scaled
up; a closely related and more delicate question is which integers — and in
particular which *primes* — are themselves sums of two squares a² + b².

**Fermat's theorem on sums of two squares** (his "Christmas theorem", 1640)
answers this for primes: a prime p is a sum of two squares if and only if
p ≢ 3 (mod 4), i.e. p = 2 or p ≡ 1 (mod 4).

This file packages the prime case as a clean biconditional:

  * the **hard forward direction** (every prime p with p % 4 ≠ 3 is a sum of two
    squares) is Mathlib's `Nat.Prime.sq_add_sq`, which goes through the
    arithmetic of the Gaussian integers ℤ[i];
  * the **easy converse** (no number ≡ 3 mod 4 is a sum of two squares) is proved
    here from scratch: squares are 0 or 1 mod 4, so a sum of two squares is
    0, 1, or 2 mod 4 — never 3.

We also record the special cases p = 2 and p ≡ 1 (mod 4), and the
Brahmagupta–Fibonacci identity exhibiting the sums of two squares as closed under
multiplication.

Status: 0 axioms, 0 sorries
-/

namespace PythagoreanTriplesOQ04

-- ============================================================================
-- Part I: The elementary mod-4 obstruction (the easy converse)
-- ============================================================================

/-- A perfect square is `0` or `1` modulo `4`. -/
theorem sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have e : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  have h : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (n % 4) <;> simp_all

/-- **The mod-4 obstruction.** A sum of two squares is never congruent to `3`
modulo `4`, because each square contributes `0` or `1`. This is the elementary
half of Fermat's two-square theorem. -/
theorem sum_two_squares_mod_four_ne_three (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb <;> omega

/-- Contrapositive packaging: if `n ≡ 3 (mod 4)` then `n` is not a sum of two
squares. -/
theorem not_sum_two_squares_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) :
    ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = n := by
  rintro ⟨a, b, rfl⟩
  exact sum_two_squares_mod_four_ne_three a b h

-- ============================================================================
-- Part II: Fermat's theorem for primes (the biconditional)
-- ============================================================================

/-- **Fermat's two-square theorem for primes.** A prime `p` is a sum of two
squares **iff** `p ≢ 3 (mod 4)`. The forward direction is the deep statement
(`Nat.Prime.sq_add_sq`, via the Gaussian integers); the converse is the
elementary mod-4 obstruction above. -/
theorem prime_sq_add_sq_iff {p : ℕ} [Fact p.Prime] :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 ≠ 3 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact sum_two_squares_mod_four_ne_three a b
  · intro h
    exact Nat.Prime.sq_add_sq h

/-- The hard direction on its own: every prime `p` with `p % 4 ≠ 3` is a sum of
two squares. -/
theorem prime_sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq hp

-- ============================================================================
-- Part III: Special cases
-- ============================================================================

/-- The prime `2 = 1² + 1²`. -/
theorem two_eq_sq_add_sq : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 2 :=
  ⟨1, 1, by norm_num⟩

/-- Every prime `p ≡ 1 (mod 4)` is a sum of two squares (the odd-prime case of
Fermat's theorem). -/
theorem prime_one_mod_four_sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq (by omega)

-- ============================================================================
-- Part IV: Multiplicative structure (Brahmagupta–Fibonacci identity)
-- ============================================================================

/-- **Brahmagupta–Fibonacci identity.** The sums of two squares are closed under
multiplication: if `m` and `n` are each a sum of two squares, so is `m * n`.
This is the multiplicative backbone that, together with Fermat's prime case,
characterizes *all* sums of two squares via their prime factorizations. -/
theorem mul_sum_two_squares {m n : ℕ}
    (hm : ∃ x y : ℕ, x ^ 2 + y ^ 2 = m) (hn : ∃ u v : ℕ, u ^ 2 + v ^ 2 = n) :
    ∃ r s : ℕ, r ^ 2 + s ^ 2 = m * n := by
  obtain ⟨x, y, hx⟩ := hm
  obtain ⟨u, v, hu⟩ := hn
  obtain ⟨r, s, h⟩ := Nat.sq_add_sq_mul hx.symm hu.symm
  exact ⟨r, s, h.symm⟩

-- ============================================================================
-- Part V: Summary
-- ============================================================================

/-
## Summary

| Result | Statement | Backing |
|--------|-----------|---------|
| `sq_mod_four` | n² ≡ 0 or 1 (mod 4) | elementary (this file) |
| `sum_two_squares_mod_four_ne_three` | a² + b² ≢ 3 (mod 4) | elementary (this file) |
| `prime_sq_add_sq_iff` | prime p is a²+b² ⟺ p ≢ 3 (mod 4) | Fermat + mod-4 |
| `prime_sq_add_sq` | p ≢ 3 (mod 4) ⟹ p = a²+b² | `Nat.Prime.sq_add_sq` |
| `mul_sum_two_squares` | sums of two squares closed under × | `Nat.sq_add_sq_mul` |

Fermat's theorem is the prime case of the full characterization: a positive
integer is a sum of two squares iff every prime ≡ 3 (mod 4) occurs to an even
power in its factorization (`Nat.eq_sq_add_sq_iff`). The biconditional packaged
here isolates the prime case, pairing Mathlib's Gaussian-integer forward
direction with the elementary mod-4 converse that this file supplies.
-/

end PythagoreanTriplesOQ04

#check @PythagoreanTriplesOQ04.prime_sq_add_sq_iff
#check @PythagoreanTriplesOQ04.sum_two_squares_mod_four_ne_three
#check @PythagoreanTriplesOQ04.mul_sum_two_squares
#check @PythagoreanTriplesOQ04.prime_one_mod_four_sq_add_sq
