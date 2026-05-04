import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Proofs.BezoutIdentityOQ02OQ01OQ02OQ02

/-
# Fermat's Two-Square Theorem (bezout-identity-oq-02-oq-01-oq-02-oq-02-oq-02)

## Open Question

Fermat's two-square theorem follows directly from the Gaussian prime classification:
p is a sum of two integer squares iff p = 2 or p ≡ 1 (mod 4).

## Answer: YES — biconditional proved with 0 sorries, 0 axioms

### Main Results

1. `fermat_two_squares_prime`: p prime is a sum of two squares ↔ p = 2 or p ≡ 1 (mod 4)
2. `fermat_two_squares_3mod4`: primes ≡ 3 (mod 4) are NOT sums of two squares
3. `fermat_two_squares_1mod4`: primes ≡ 1 (mod 4) ARE sums of two squares
4. Concrete examples: 2=1²+1², 5=2²+1², 13=3²+2², 17=4²+1²
5. Non-examples: 3, 7, 11 (≡ 3 mod 4) have no two-square representation

## Proof Strategy

**Direction (←):**
- p = 2: direct computation 1² + 1² = 2
- p ≡ 1 (mod 4): Mathlib's `Nat.Prime.sq_add_sq` (p % 4 ≠ 3 → ∃ a b, a² + b² = p)

**Direction (→):**
- Assume a² + b² = p and show ¬(p % 4 = 3)
- Squares mod 4 are 0 or 1 → sum ∈ {0,1,2} ≠ 3 (proved by `decide` over ZMod 4)
- p odd prime → p % 4 ∈ {1,3} → since ≢ 3, must be 1

## Connection to Gaussian Integers

The parent file proved:
- p ≡ 3 (mod 4) → p is irreducible (inert) in ℤ[i] → no a²+b²=p
- p ≡ 1 (mod 4) → p splits in ℤ[i] as z·z̄ with norm(z)=p → p = re²+im²

This theorem is the direct statement of that classification for rational primes.

## Builds On
- BezoutIdentityOQ02OQ01OQ02OQ02.lean: Gaussian prime classification
- Mathlib: Nat.Prime.sq_add_sq, ZMod arithmetic
-/

namespace FermatTwoSquare

-- ============================================================
-- PART 1: Squares mod 4 helper
-- ============================================================

/-- Squares mod 4 are only 0 or 1; their sum cannot be 3. Proved by decide. -/
private lemma sum_sq_ne_three_mod4 (a b : ZMod 4) : a ^ 2 + b ^ 2 ≠ 3 := by decide

-- ============================================================
-- PART 2: Main Theorem — Fermat's Two-Square Theorem
-- ============================================================

/-- **Fermat's Two-Square Theorem** (full biconditional):

    A prime p is expressible as p = a² + b² (integers a, b) iff p = 2 or p ≡ 1 (mod 4).

    Equivalently: primes expressible as sums of two squares are exactly 2 and
    primes of the form 4k+1. -/
theorem fermat_two_squares_prime {p : ℕ} (hp : Nat.Prime p) :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, hab⟩
    -- First show p % 4 ≠ 3 (squares mod 4 argument)
    have hmod_ne3 : p % 4 ≠ 3 := by
      intro h3
      have h4 : (a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2 = (p : ZMod 4) := by
        have := congr_arg (Int.cast : ℤ → ZMod 4) hab
        push_cast at this ⊢; exact this
      have hp4 : (p : ZMod 4) = 3 := by
        rw [show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) from by norm_num,
            ZMod.natCast_eq_natCast_iff]
        exact h3
      exact sum_sq_ne_three_mod4 (a : ZMod 4) (b : ZMod 4) (hp4 ▸ h4)
    -- p = 2 (even prime) or p is odd with p % 4 = 1
    by_cases hp2 : p = 2
    · left; exact hp2
    · right
      -- Odd primes have p % 4 ∈ {1, 3}; ruled out 3 above
      have hodd : Odd p := hp.odd_of_ne_two hp2
      obtain ⟨m, hm⟩ := hodd
      have hmod13 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hmod13 with h1 | h3
      · exact h1
      · exact absurd h3 hmod_ne3
  · rintro (rfl | h1)
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact (Nat.Prime p) := ⟨hp⟩
      exact Nat.Prime.sq_add_sq (by omega)

-- ============================================================
-- PART 3: Corollaries
-- ============================================================

/-- Primes ≡ 3 (mod 4) are never sums of two integer squares. -/
theorem fermat_two_squares_3mod4 {p : ℕ} (hp : Nat.Prime p) (h3 : p % 4 = 3) :
    ¬ ∃ a b : ℤ, a ^ 2 + b ^ 2 = p := by
  rw [fermat_two_squares_prime hp]
  rintro (rfl | h1)
  · norm_num at h3
  · omega

/-- Primes ≡ 1 (mod 4) are always sums of two integer squares. -/
theorem fermat_two_squares_1mod4 {p : ℕ} (hp : Nat.Prime p) (h1 : p % 4 = 1) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = p :=
  (fermat_two_squares_prime hp).mpr (Or.inr h1)

/-- Equivalent form: a prime is a sum of two squares iff it is NOT ≡ 3 (mod 4). -/
theorem fermat_iff_not_3mod4 {p : ℕ} (hp : Nat.Prime p) :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = p) ↔ ¬ (p % 4 = 3) := by
  rw [fermat_two_squares_prime hp]
  constructor
  · rintro (rfl | h1) h3
    · norm_num at h3
    · omega
  · intro h
    by_cases hp2 : p = 2
    · left; exact hp2
    · right
      have hodd : Odd p := hp.odd_of_ne_two hp2
      obtain ⟨m, hm⟩ := hodd
      have hmod13 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hmod13 with h1 | h3
      · exact h1
      · exact absurd h3 h

-- ============================================================
-- PART 4: Concrete Examples
-- ============================================================

theorem fermat_2 : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 2 := ⟨1, 1, by norm_num⟩
theorem fermat_5 : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 5 := ⟨2, 1, by norm_num⟩
theorem fermat_13 : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 13 := ⟨3, 2, by norm_num⟩
theorem fermat_17 : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 17 := ⟨4, 1, by norm_num⟩
theorem fermat_29 : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 29 := ⟨5, 2, by norm_num⟩

theorem fermat_3_neg : ¬ ∃ a b : ℤ, a ^ 2 + b ^ 2 = 3 :=
  fermat_two_squares_3mod4 (by norm_num) (by norm_num)

theorem fermat_7_neg : ¬ ∃ a b : ℤ, a ^ 2 + b ^ 2 = 7 :=
  fermat_two_squares_3mod4 (by norm_num) (by norm_num)

theorem fermat_11_neg : ¬ ∃ a b : ℤ, a ^ 2 + b ^ 2 = 11 :=
  fermat_two_squares_3mod4 (by norm_num) (by norm_num)

theorem fermat_19_neg : ¬ ∃ a b : ℤ, a ^ 2 + b ^ 2 = 19 :=
  fermat_two_squares_3mod4 (by norm_num) (by norm_num)

end FermatTwoSquare
