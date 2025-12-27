import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Fermat's Sum of Two Squares Theorem

## What This Proves
We prove Fermat's theorem on sums of two squares: A prime p can be expressed as the
sum of two squares (p = a² + b²) if and only if p = 2 or p ≡ 1 (mod 4).

## Historical Context
Fermat stated this theorem around 1640 but never published a proof. The first complete
proof was given by Euler in 1747, over a century later. This theorem is one of the
foundational results in algebraic number theory.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Nat.Prime.sq_add_sq` which provides
  the complete characterization. Mathlib contains two independent proofs:
  1. Zagier's "one-sentence proof" (Archive/ZagierTwoSquares.lean)
  2. Gaussian integer proof (Mathlib/NumberTheory/SumTwoSquares.lean)
- **Original Contributions:** We provide pedagogical wrapper theorems and corollaries
  that highlight the key insights and special cases.

## The Zagier Proof (Featured Approach)
Zagier's proof is remarkably elegant. For a prime p ≡ 1 (mod 4):
1. Define S = {(x,y,z) ∈ ℕ³ | x² + 4yz = p}
2. Show S is finite with |S| odd (since p is odd)
3. Define two involutions on S:
   - The "obvious" involution: (x,y,z) ↦ (x,z,y)
   - The "complex" involution with exactly one fixed point
4. Since |S| is odd, both involutions must have fixed points
5. A fixed point of the obvious involution gives y = z, hence p = x² + 4y² = x² + (2y)²

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Nat.Prime.sq_add_sq` : Main characterization theorem
- `ZMod` : Modular arithmetic for p % 4 conditions
- `Nat.Prime` : Prime number definitions

## References
- [Zagier's One-Sentence Proof (1990)](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.2307/2323918/fulltext.pdf)
- Wiedijk 100 Theorems #20
-/

namespace FermatTwoSquares

/-! ## The Main Theorem -/

/-- **Fermat's Sum of Two Squares Theorem (Main Statement)**

A prime p can be expressed as a sum of two squares p = a² + b²
if and only if p ≠ 3 (mod 4).

Equivalently: p = 2 or p ≡ 1 (mod 4).

This is Mathlib's statement of the theorem, using `p % 4 ≠ 3` as the condition. -/
theorem sum_two_squares_iff_not_three_mod_four {p : ℕ} [hp : Fact p.Prime] :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 ≠ 3 := by
  constructor
  · -- If p = a² + b², then p % 4 ≠ 3
    intro ⟨a, b, hab⟩
    intro h
    -- Squares modulo 4 can only be 0 or 1
    -- So a² + b² ≡ 0, 1, or 2 (mod 4), never 3
    have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      have : a % 4 < 4 := Nat.mod_lt a (by omega)
      interval_cases a % 4 <;> simp [Nat.pow_mod]
    have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
      have : b % 4 < 4 := Nat.mod_lt b (by omega)
      interval_cases b % 4 <;> simp [Nat.pow_mod]
    have hsum : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
    rw [hab] at hsum
    exact hsum h
  · -- If p % 4 ≠ 3, then p = a² + b²
    exact Nat.Prime.sq_add_sq hp.out

/-- **Special Case: Primes Congruent to 1 (mod 4)**

Every prime p ≡ 1 (mod 4) is a sum of two squares.
This is the classic statement of Fermat's theorem. -/
theorem one_mod_four_is_sum_of_squares {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  apply Nat.Prime.sq_add_sq
  omega

/-- **Special Case: The Prime 2**

2 = 1² + 1² is trivially a sum of two squares.
Note: 2 ≡ 2 (mod 4), which is neither 1 nor 3. -/
theorem two_is_sum_of_squares : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 2 :=
  ⟨1, 1, rfl⟩

/-- **Negative Result: Primes Congruent to 3 (mod 4)**

No prime p ≡ 3 (mod 4) can be expressed as a sum of two squares.

Proof: Squares modulo 4 are either 0 or 1.
- 0² ≡ 0 (mod 4)
- 1² ≡ 1 (mod 4)
- 2² ≡ 0 (mod 4)
- 3² ≡ 1 (mod 4)

So a² + b² ≡ 0, 1, or 2 (mod 4). It can never be 3. -/
theorem three_mod_four_not_sum_of_squares {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    ¬∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  intro ⟨a, b, hab⟩
  -- Squares mod 4 are 0 or 1
  have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
    have : a % 4 < 4 := Nat.mod_lt a (by omega)
    interval_cases a % 4 <;> simp [Nat.pow_mod]
  have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
    have : b % 4 < 4 := Nat.mod_lt b (by omega)
    interval_cases b % 4 <;> simp [Nat.pow_mod]
  -- So their sum mod 4 is 0, 1, or 2
  have hsum : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
  rw [hab] at hsum
  exact hsum hp

/-! ## Examples -/

/-- 5 = 1² + 2² (since 5 ≡ 1 mod 4) -/
example : (1 : ℕ) ^ 2 + 2 ^ 2 = 5 := rfl

/-- 13 = 2² + 3² (since 13 ≡ 1 mod 4) -/
example : (2 : ℕ) ^ 2 + 3 ^ 2 = 13 := rfl

/-- 17 = 1² + 4² (since 17 ≡ 1 mod 4) -/
example : (1 : ℕ) ^ 2 + 4 ^ 2 = 17 := rfl

/-- 29 = 2² + 5² (since 29 ≡ 1 mod 4) -/
example : (2 : ℕ) ^ 2 + 5 ^ 2 = 29 := rfl

/-- 37 = 1² + 6² (since 37 ≡ 1 mod 4) -/
example : (1 : ℕ) ^ 2 + 6 ^ 2 = 37 := rfl

/-- 41 = 4² + 5² (since 41 ≡ 1 mod 4) -/
example : (4 : ℕ) ^ 2 + 5 ^ 2 = 41 := rfl

/-! ## Classification of All Primes -/

/-- **Complete Classification of Primes**

For any prime p, exactly one of these holds:
1. p = 2 (and 2 = 1² + 1²)
2. p ≡ 1 (mod 4) (and p is a sum of two squares)
3. p ≡ 3 (mod 4) (and p is NOT a sum of two squares) -/
theorem prime_classification (p : ℕ) [Fact p.Prime] :
    (p = 2 ∨ p % 4 = 1) ∨ p % 4 = 3 := by
  have hp2 : p ≥ 2 := Nat.Prime.two_le (Fact.out)
  have hmod4 : p % 4 < 4 := Nat.mod_lt p (by omega)
  interval_cases p % 4
  · -- p % 4 = 0 means 4 | p
    left; left
    have hdiv : 4 ∣ p := Nat.dvd_of_mod_eq_zero rfl
    have hprime := (Fact.out : p.Prime)
    have := hprime.eq_one_or_self_of_dvd 4 hdiv
    rcases this with h1 | h4
    · omega
    · omega
  · -- p % 4 = 1
    left; right; rfl
  · -- p % 4 = 2 means 2 | p
    left; left
    have hdiv : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega : p % 2 = 0)
    have hprime := (Fact.out : p.Prime)
    have := hprime.eq_one_or_self_of_dvd 2 hdiv
    rcases this with h1 | h2
    · omega
    · exact h2
  · -- p % 4 = 3
    right; rfl

/-- **Sum of Two Squares iff Not 3 mod 4 (Corollary)**

Restating the main theorem using the classification. -/
theorem sum_of_squares_classification (p : ℕ) [Fact p.Prime] :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · intro h
    have hne3 : p % 4 ≠ 3 := sum_two_squares_iff_not_three_mod_four.mp h
    have hclass := prime_classification p
    rcases hclass with (hclass | hclass)
    · exact hclass
    · exact absurd hclass hne3
  · intro h
    rcases h with rfl | h1
    · exact two_is_sum_of_squares
    · exact one_mod_four_is_sum_of_squares h1

#check sum_two_squares_iff_not_three_mod_four
#check one_mod_four_is_sum_of_squares
#check three_mod_four_not_sum_of_squares
#check sum_of_squares_classification

end FermatTwoSquares
