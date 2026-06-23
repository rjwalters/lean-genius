import Mathlib.Tactic
import Proofs.LagrangeFourSquares

/-
# Legendre-Gauss Three-Square Theorem (OQ-04)

## Open Question
Formalize the three-square theorem: n = a² + b² + c² iff n ≠ 4^a(8b+7).

## What This Proves
The FORWARD direction: numbers of the form 4^a(8b+7) are NOT sums of three squares.

This is proved from first principles using two key lemmas:
1. Squares mod 8 are in {0, 1, 4}, so three squares mod 8 ≠ 7 (base case)
2. If 4 | (x²+y²+z²), then 2|x, 2|y, 2|z (descent step)

The backward direction (every number NOT of that form IS a sum of three squares)
requires Gauss's genus theory for ternary quadratic forms and is axiomatized.

## Axiom Count: 1
- not_obstructed_is_three_squares: ¬IsObstructed n → IsSumOfThreeSquares n

The parent LagrangeFourSquares.lean axiomatized the FULL biconditional.
This file replaces half of that axiom with a proof.
-/

open LagrangeFourSquares

namespace ThreeSquareTheorem

-- ═══════════════════════════════════════════════════════════════
-- SECTION I: Squares Modulo 8
-- ═══════════════════════════════════════════════════════════════

/-- Squares mod 4 are 0 or 1. -/
theorem sq_mod_4 (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have h : a ^ 2 % 4 = (a % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  rw [h]
  have : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 4) <;> norm_num

/-- Squares mod 8 are in {0, 1, 4}. This is the key modular constraint:
    0² ≡ 0, 1² ≡ 1, 2² ≡ 4, 3² ≡ 1, 4² ≡ 0, 5² ≡ 1, 6² ≡ 4, 7² ≡ 1 (mod 8). -/
theorem sq_mod_8 (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  rw [h]
  have : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 8) <;> norm_num

/-- The sum of three squares modulo 8 is never 7.

    Proof: each square mod 8 ∈ {0, 1, 4}. The maximum achievable values mod 8:
    0+0+0=0, 0+0+1=1, 0+0+4=4, 0+1+1=2, 0+1+4=5, 0+4+4=0,
    1+1+1=3, 1+1+4=6, 1+4+4=1, 4+4+4=4. Never 7. -/
theorem three_sq_not_7_mod_8 (a b c : ℕ) : (a ^ 2 + b ^ 2 + c ^ 2) % 8 ≠ 7 := by
  have ha := sq_mod_8 a
  have hb := sq_mod_8 b
  have hc := sq_mod_8 c
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;> omega

-- ═══════════════════════════════════════════════════════════════
-- SECTION II: Descent Lemma
-- ═══════════════════════════════════════════════════════════════

/-- If x² ≡ 0 (mod 4), then x is even.
    Contrapositive: x odd ⇒ x² ≡ 1 (mod 4). -/
private theorem even_of_sq_mod_4_eq_0 {x : ℕ} (h : x ^ 2 % 4 = 0) : 2 ∣ x := by
  by_contra hx
  have : x % 2 = 1 := by omega
  have key : x ^ 2 % 4 = (x % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  rw [key] at h
  have : x % 4 = 1 ∨ x % 4 = 3 := by omega
  rcases this with h' | h' <;> rw [h'] at h <;> norm_num at h

/-- If 4 divides a sum of three squares, then each summand is even.

    Proof: squares mod 4 are {0, 1}. For three values from {0,1} to sum
    to 0 mod 4: 0+0+0=0 ✓, 0+0+1=1 ✗, 0+1+1=2 ✗, 1+1+1=3 ✗.
    So all three must be ≡ 0 (mod 4), i.e., x², y², z² are divisible by 4,
    meaning x, y, z are even. -/
theorem four_dvd_three_sq {x y z : ℕ} (h : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  have hx := sq_mod_4 x
  have hy := sq_mod_4 y
  have hz := sq_mod_4 z
  obtain ⟨k, hk⟩ := h
  have hx0 : x ^ 2 % 4 = 0 := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> omega
  have hy0 : y ^ 2 % 4 = 0 := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> omega
  have hz0 : z ^ 2 % 4 = 0 := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> omega
  exact ⟨even_of_sq_mod_4_eq_0 hx0, even_of_sq_mod_4_eq_0 hy0, even_of_sq_mod_4_eq_0 hz0⟩

-- ═══════════════════════════════════════════════════════════════
-- SECTION III: Forward Direction
-- ═══════════════════════════════════════════════════════════════

/-- **Base case**: Numbers ≡ 7 (mod 8) are not sums of three squares. -/
theorem not_three_sq_of_7_mod_8 {n : ℕ} (hn : n % 8 = 7) :
    ¬IsSumOfThreeSquares n := by
  intro ⟨a, b, c, h⟩
  have := three_sq_not_7_mod_8 a b c
  rw [h] at this
  exact this hn

/-- **Forward direction of the three-square theorem** (fully proved):
    Numbers of the form 4^a(8b+7) are NOT sums of three squares.

    Proof by induction on a:
    - Base (a=0): n = 8b+7 ≡ 7 (mod 8), impossible by three_sq_not_7_mod_8.
    - Step (a→a+1): n = 4^{a+1}(8b+7). If n = x²+y²+z², then 4|(x²+y²+z²),
      so 2|x, 2|y, 2|z by four_dvd_three_sq. Then n/4 = (x/2)²+(y/2)²+(z/2)²
      = 4^a(8b+7), contradicting the induction hypothesis. -/
theorem obstructed_not_three_squares (n : ℕ) (h : IsObstructed n) :
    ¬IsSumOfThreeSquares n := by
  obtain ⟨a, b, rfl⟩ := h
  induction a with
  | zero =>
    simp
    exact not_three_sq_of_7_mod_8 (by omega)
  | succ a ih =>
    intro ⟨x, y, z, heq⟩
    have h4 : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2 := by
      rw [heq]; exact ⟨4 ^ a * (8 * b + 7), by ring⟩
    have ⟨⟨x', hx⟩, ⟨y', hy⟩, ⟨z', hz⟩⟩ := four_dvd_three_sq h4
    rw [hx, hy, hz] at heq
    have heq' : x' ^ 2 + y' ^ 2 + z' ^ 2 = 4 ^ a * (8 * b + 7) := by nlinarith
    exact ih ⟨x', y', z', heq'⟩

-- ═══════════════════════════════════════════════════════════════
-- SECTION IV: Backward Direction (axiom)
-- ═══════════════════════════════════════════════════════════════

/-- **Backward direction** (axiomatized):
    If n is NOT of the form 4^a(8b+7), then n IS a sum of three squares.

    This is the hard direction, proved by Legendre (1798) and Gauss (1801).
    It requires the theory of ternary quadratic forms and genus theory:
    one must show that the genus of x² + y² + z² represents n by checking
    local conditions at all primes, then show each genus class has a
    representative that achieves the representation. -/
axiom not_obstructed_is_three_squares :
    ∀ n : ℕ, ¬IsObstructed n → IsSumOfThreeSquares n

-- ═══════════════════════════════════════════════════════════════
-- SECTION V: Complete Theorem
-- ═══════════════════════════════════════════════════════════════

/-- **Legendre-Gauss Three-Square Theorem**:
    n is a sum of three squares if and only if n is NOT of the form 4^a(8b+7).

    Forward direction: proved (obstructed_not_three_squares).
    Backward direction: axiomatized (not_obstructed_is_three_squares). -/
theorem legendre_three_squares' (n : ℕ) :
    IsSumOfThreeSquares n ↔ ¬IsObstructed n := by
  constructor
  · exact fun h hobs => obstructed_not_three_squares n hobs h
  · exact not_obstructed_is_three_squares n

-- ═══════════════════════════════════════════════════════════════
-- SECTION VI: Corollaries
-- ═══════════════════════════════════════════════════════════════

/-- Every number not divisible by 4 and not ≡ 7 (mod 8) is a sum of three squares. -/
theorem three_sq_of_not_7_mod_8 {n : ℕ} (hn : n % 8 ≠ 7) (h4 : ¬(4 ∣ n) ∨ n = 0) :
    IsSumOfThreeSquares n := by
  apply not_obstructed_is_three_squares
  intro ⟨a, b, hab⟩
  cases a with
  | zero => simp at hab; omega
  | succ a =>
    rcases h4 with h4 | rfl
    · exact h4 ⟨4 ^ a * (8 * b + 7), by ring⟩
    · simp at hab

/-- Numbers ≡ 1 (mod 8) are always three-square (not obstructed since 1 ≠ 7 mod 8). -/
theorem three_sq_1_mod_8 (k : ℕ) : IsSumOfThreeSquares (8 * k + 1) := by
  apply not_obstructed_is_three_squares
  intro ⟨a, b, hab⟩
  cases a with
  | zero => omega
  | succ a =>
    -- 4^{a+1}(8b+7) is divisible by 4, but 8k+1 ≡ 1 mod 4
    have h2 : 4 ∣ (8 * k + 1) := by
      rw [hab]; exact dvd_mul_of_dvd_left (dvd_pow_self 4 (Nat.succ_ne_zero a)) _
    obtain ⟨m, hm⟩ := h2
    omega

/-- The three-square and four-square theorems together:
    every number is a sum of three OR four squares, and exactly those
    of the form 4^a(8b+7) need the fourth square. -/
theorem three_or_four_squares (n : ℕ) :
    IsSumOfThreeSquares n ∨ (IsObstructed n ∧ ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = n) := by
  by_cases h : IsObstructed n
  · exact Or.inr ⟨h, lagrange_four_squares n⟩
  · exact Or.inl ((legendre_three_squares' n).mpr h)

/-- The proportion of numbers needing four squares: 1/6 of all residue classes mod 8
    are obstructed (just residue 7), so asymptotically about 1/6 of numbers
    need four squares. Here we verify the small cases. -/
example : ¬IsSumOfThreeSquares 7 := by
  apply obstructed_not_three_squares; exact ⟨0, 0, by norm_num⟩

example : ¬IsSumOfThreeSquares 15 := by
  apply obstructed_not_three_squares; exact ⟨0, 1, by norm_num⟩

example : ¬IsSumOfThreeSquares 28 := by
  apply obstructed_not_three_squares; exact ⟨1, 0, by norm_num⟩

example : ¬IsSumOfThreeSquares 112 := by
  apply obstructed_not_three_squares; exact ⟨2, 0, by norm_num⟩

-- ═══════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════

#check sq_mod_8
#check three_sq_not_7_mod_8
#check four_dvd_three_sq
#check obstructed_not_three_squares
#check not_obstructed_is_three_squares
#check legendre_three_squares'

end ThreeSquareTheorem
