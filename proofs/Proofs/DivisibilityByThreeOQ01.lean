/-
Formal Divisibility Rules for Various Bases and Moduli - Extension OQ-01

Extends DivisibilityBy3 and DivisibilityRules with:
1. General last-k-digits theorem (unifying 2/4/8/5/25/125 rules)
2. Power-of-2 and power-of-5 general theorems
3. Divisibility by 13 via truncation method
4. Divisibility by 37 via three-digit grouping
5. Casting out nines / threes theory
6. Digital root theory and properties
7. Additional digit-sum instantiations (base 100, 1000)
8. Coprime factorization rules (6, 12, 15, 18, 36, 45, 60, 90)

Tags: number-theory, modular-arithmetic, divisibility, extension
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

open Nat

namespace DivisibilityByThreeOQ01

-- ============================================================
-- Part I: General Last-k-Digits Theorem
-- ============================================================

/-- **General last-k-digits rule**: If d | M, then d | n ↔ d | (n % M).

    This unifies all "last k digits" divisibility rules:
    - div by 2 (M=10): 2 | 10
    - div by 4 (M=100): 4 | 100
    - div by 8 (M=1000): 8 | 1000
    - div by 5 (M=10): 5 | 10
    - div by 25 (M=100): 25 | 100
    - div by 125 (M=1000): 125 | 1000 -/
theorem dvd_iff_dvd_mod (d M n : ℕ) (hdM : d ∣ M) : d ∣ n ↔ d ∣ (n % M) := by
  constructor
  · intro hdn
    have hmod : n % M % d = 0 := by
      obtain ⟨c, rfl⟩ := hdM
      obtain ⟨k, rfl⟩ := hdn
      simp [Nat.mul_mod_right]
    exact Nat.dvd_of_mod_eq_zero hmod
  · intro hmod
    have key : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
    rw [key]
    exact Nat.dvd_add (dvd_trans hdM (dvd_mul_right M (n / M))) hmod

/-- Divisibility by 2 via last decimal digit -/
theorem two_dvd_last1 (n : ℕ) : 2 ∣ n ↔ 2 ∣ (n % 10) :=
  dvd_iff_dvd_mod 2 10 n ⟨5, by ring⟩

/-- Divisibility by 4 via last two decimal digits -/
theorem four_dvd_last2 (n : ℕ) : 4 ∣ n ↔ 4 ∣ (n % 100) :=
  dvd_iff_dvd_mod 4 100 n ⟨25, by ring⟩

/-- Divisibility by 8 via last three decimal digits -/
theorem eight_dvd_last3 (n : ℕ) : 8 ∣ n ↔ 8 ∣ (n % 1000) :=
  dvd_iff_dvd_mod 8 1000 n ⟨125, by ring⟩

/-- Divisibility by 16 via last four decimal digits -/
theorem sixteen_dvd_last4 (n : ℕ) : 16 ∣ n ↔ 16 ∣ (n % 10000) :=
  dvd_iff_dvd_mod 16 10000 n ⟨625, by ring⟩

/-- Divisibility by 32 via last five decimal digits -/
theorem thirtytwo_dvd_last5 (n : ℕ) : 32 ∣ n ↔ 32 ∣ (n % 100000) :=
  dvd_iff_dvd_mod 32 100000 n ⟨3125, by ring⟩

/-- Divisibility by 5 via last decimal digit -/
theorem five_dvd_last1 (n : ℕ) : 5 ∣ n ↔ 5 ∣ (n % 10) :=
  dvd_iff_dvd_mod 5 10 n ⟨2, by ring⟩

/-- Divisibility by 25 via last two decimal digits -/
theorem twentyfive_dvd_last2 (n : ℕ) : 25 ∣ n ↔ 25 ∣ (n % 100) :=
  dvd_iff_dvd_mod 25 100 n ⟨4, by ring⟩

/-- Divisibility by 125 via last three decimal digits -/
theorem onehundredtwentyfive_dvd_last3 (n : ℕ) : 125 ∣ n ↔ 125 ∣ (n % 1000) :=
  dvd_iff_dvd_mod 125 1000 n ⟨8, by ring⟩

-- Binary base
/-- Divisibility by 4 via last 2 bits -/
theorem four_dvd_binary (n : ℕ) : 4 ∣ n ↔ 4 ∣ (n % 4) :=
  dvd_iff_dvd_mod 4 4 n ⟨1, by ring⟩

/-- Divisibility by 8 via last 3 bits -/
theorem eight_dvd_binary (n : ℕ) : 8 ∣ n ↔ 8 ∣ (n % 8) :=
  dvd_iff_dvd_mod 8 8 n ⟨1, by ring⟩

-- Hexadecimal base
/-- Divisibility by 256 via last 2 hex digits -/
theorem twofiftysix_dvd_hex2 (n : ℕ) : 256 ∣ n ↔ 256 ∣ (n % 256) :=
  dvd_iff_dvd_mod 256 256 n ⟨1, by ring⟩

-- ============================================================
-- Part II: Power-of-2 and Power-of-5 General Theorems
-- ============================================================

/-- Powers of 2 divide powers of 10: 2^k | 10^k -/
theorem pow2_dvd_pow10 (k : ℕ) : 2 ^ k ∣ 10 ^ k := by
  have : (10 : ℕ) = 2 * 5 := by norm_num
  rw [this, mul_pow]
  exact dvd_mul_right (2 ^ k) (5 ^ k)

/-- Powers of 5 divide powers of 10: 5^k | 10^k -/
theorem pow5_dvd_pow10 (k : ℕ) : 5 ^ k ∣ 10 ^ k := by
  have : (10 : ℕ) = 2 * 5 := by norm_num
  rw [this, mul_pow]
  exact dvd_mul_left (5 ^ k) (2 ^ k)

/-- General: 2^k | n ↔ 2^k | (n mod 10^k) -/
theorem pow2_dvd_last_k (k n : ℕ) : 2 ^ k ∣ n ↔ 2 ^ k ∣ (n % 10 ^ k) :=
  dvd_iff_dvd_mod _ _ n (pow2_dvd_pow10 k)

/-- General: 5^k | n ↔ 5^k | (n mod 10^k) -/
theorem pow5_dvd_last_k (k n : ℕ) : 5 ^ k ∣ n ↔ 5 ^ k ∣ (n % 10 ^ k) :=
  dvd_iff_dvd_mod _ _ n (pow5_dvd_pow10 k)

-- ============================================================
-- Part III: Divisibility by 13 (Truncation Method)
-- ============================================================

/-- **Divisibility by 13 via truncation**: 13 | n ↔ 13 | (n/10 + 4·(n%10)).

    Proof: 10(q + 4r) = 10q + 40r = (n - r) + 40r = n + 39r ≡ n (mod 13),
    and gcd(13, 10) = 1.
    This is the "add 4 times the last digit" rule for 13. -/
theorem thirteen_dvd_truncation (n : ℕ) :
    13 ∣ n ↔ (13 : ℤ) ∣ (↑(n / 10) + 4 * ↑(n % 10)) := by
  constructor
  · intro ⟨k, hk⟩
    have key : (10 : ℤ) * (↑(n / 10) + 4 * ↑(n % 10)) = ↑n + 39 * ↑(n % 10) := by
      push_cast; omega
    have h39 : (13 : ℤ) ∣ (↑n + 39 * ↑(n % 10)) :=
      ⟨↑k + 3 * ↑(n % 10), by push_cast; omega⟩
    rw [← key] at h39
    exact IsCoprime.dvd_of_dvd_mul_left (by decide : IsCoprime (13 : ℤ) 10) h39
  · intro h13
    have key : (10 : ℤ) * (↑(n / 10) + 4 * ↑(n % 10)) = ↑n + 39 * ↑(n % 10) := by
      push_cast; omega
    have h10 : (13 : ℤ) ∣ (10 * (↑(n / 10) + 4 * ↑(n % 10))) :=
      dvd_mul_of_dvd_right h13 10
    rw [key] at h10
    have h39 : (13 : ℤ) ∣ (39 * ↑(n % 10)) := ⟨3 * ↑(n % 10), by ring⟩
    have hsub := Int.dvd_sub h10 h39
    simp only [add_sub_cancel_right] at hsub
    exact_mod_cast hsub

-- Verification
example : 13 ∣ 169 := by native_decide
example : 13 ∣ 1001 := by native_decide
example : ¬(13 ∣ 100) := by native_decide

-- ============================================================
-- Part IV: Digit-Sum Rules via Mathlib
-- ============================================================

/-- Helper: d | n ↔ d | (digits b n).sum when b ≡ 1 (mod d).
    Uses Nat.modEq_digits_sum from Mathlib. -/
theorem digitSum_dvd_iff (d b : ℕ) (hdb : b % d = 1) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum :=
  Nat.ModEq.dvd_iff (Nat.modEq_digits_sum d b hdb n) (dvd_refl d)

/-- **Divisibility by 37 via three-digit groups**: Since 1000 ≡ 1 (mod 37),
    37 | n iff 37 divides the sum of consecutive three-digit groups. -/
theorem thirtyseven_dvd_base1000 (n : ℕ) :
    37 ∣ n ↔ 37 ∣ (Nat.digits 1000 n).sum :=
  digitSum_dvd_iff 37 1000 (by native_decide) n

/-- **Divisibility by 99 via two-digit groups** (base 100):
    Since 100 ≡ 1 (mod 99) -/
theorem ninetynine_dvd_base100 (n : ℕ) :
    99 ∣ n ↔ 99 ∣ (Nat.digits 100 n).sum :=
  digitSum_dvd_iff 99 100 (by native_decide) n

/-- **Divisibility by 999 via three-digit groups** (base 1000) -/
theorem nineninenine_dvd_base1000 (n : ℕ) :
    999 ∣ n ↔ 999 ∣ (Nat.digits 1000 n).sum :=
  digitSum_dvd_iff 999 1000 (by native_decide) n

/-- **Divisibility by 27 via three-digit groups** (base 1000) -/
theorem twentyseven_dvd_base1000 (n : ℕ) :
    27 ∣ n ↔ 27 ∣ (Nat.digits 1000 n).sum :=
  digitSum_dvd_iff 27 1000 (by native_decide) n

/-- **Divisibility by 7 in octal**: 8 ≡ 1 (mod 7) -/
theorem seven_dvd_octal (n : ℕ) : 7 ∣ n ↔ 7 ∣ (Nat.digits 8 n).sum :=
  digitSum_dvd_iff 7 8 (by native_decide) n

/-- **Divisibility by 3 in hex**: 16 ≡ 1 (mod 3) -/
theorem three_dvd_hex (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 16 n).sum :=
  digitSum_dvd_iff 3 16 (by native_decide) n

/-- **Divisibility by 5 in hex**: 16 ≡ 1 (mod 5) -/
theorem five_dvd_hex (n : ℕ) : 5 ∣ n ↔ 5 ∣ (Nat.digits 16 n).sum :=
  digitSum_dvd_iff 5 16 (by native_decide) n

/-- **Divisibility by 15 in hex**: 16 ≡ 1 (mod 15) -/
theorem fifteen_dvd_hex (n : ℕ) : 15 ∣ n ↔ 15 ∣ (Nat.digits 16 n).sum :=
  digitSum_dvd_iff 15 16 (by native_decide) n

/-- **Divisibility by 3 in base 7**: 7 ≡ 1 (mod 3) -/
theorem three_dvd_base7 (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 7 n).sum :=
  digitSum_dvd_iff 3 7 (by native_decide) n

/-- **Divisibility by 6 in base 7**: 7 ≡ 1 (mod 6) -/
theorem six_dvd_base7 (n : ℕ) : 6 ∣ n ↔ 6 ∣ (Nat.digits 7 n).sum :=
  digitSum_dvd_iff 6 7 (by native_decide) n

-- Verification examples
example : 37 ∣ 999 := by native_decide
example : 37 ∣ 111 := by native_decide
example : 37 ∣ 111111 := by native_decide
example : 99 ∣ 9999 := by native_decide
example : 27 ∣ 999 := by native_decide

-- ============================================================
-- Part V: Casting Out Nines / Threes
-- ============================================================

/-- **Casting out nines**: n ≡ digitSum(n) (mod 9).
    The remainder when dividing by 9 equals the remainder of the digit sum mod 9. -/
theorem casting_out_nines (n : ℕ) :
    n ≡ (Nat.digits 10 n).sum [MOD 9] :=
  Nat.modEq_digits_sum 9 10 (by native_decide) n

/-- **Casting out nines for addition**: digit sum preserves addition mod 9 -/
theorem casting_out_nines_add (a b : ℕ) :
    (a + b) ≡ ((Nat.digits 10 a).sum + (Nat.digits 10 b).sum) [MOD 9] :=
  Nat.ModEq.add (casting_out_nines a) (casting_out_nines b)

/-- **Casting out nines for multiplication**: digit sum preserves multiplication mod 9 -/
theorem casting_out_nines_mul (a b : ℕ) :
    (a * b) ≡ ((Nat.digits 10 a).sum * (Nat.digits 10 b).sum) [MOD 9] :=
  Nat.ModEq.mul (casting_out_nines a) (casting_out_nines b)

/-- **Casting out threes**: n ≡ digitSum(n) (mod 3) -/
theorem casting_out_threes (n : ℕ) :
    n ≡ (Nat.digits 10 n).sum [MOD 3] :=
  Nat.modEq_digits_sum 3 10 (by native_decide) n

/-- **Casting out threes for addition** -/
theorem casting_out_threes_add (a b : ℕ) :
    (a + b) ≡ ((Nat.digits 10 a).sum + (Nat.digits 10 b).sum) [MOD 3] :=
  Nat.ModEq.add (casting_out_threes a) (casting_out_threes b)

/-- **Casting out threes for multiplication** -/
theorem casting_out_threes_mul (a b : ℕ) :
    (a * b) ≡ ((Nat.digits 10 a).sum * (Nat.digits 10 b).sum) [MOD 3] :=
  Nat.ModEq.mul (casting_out_threes a) (casting_out_threes b)

/-- **General digit-sum congruence for addition** -/
theorem digit_sum_add_modEq (d b : ℕ) (hb : b % d = 1) (a c : ℕ) :
    (a + c) ≡ ((Nat.digits b a).sum + (Nat.digits b c).sum) [MOD d] :=
  Nat.ModEq.add (Nat.modEq_digits_sum d b hb a) (Nat.modEq_digits_sum d b hb c)

/-- **General digit-sum congruence for multiplication** -/
theorem digit_sum_mul_modEq (d b : ℕ) (hb : b % d = 1) (a c : ℕ) :
    (a * c) ≡ ((Nat.digits b a).sum * (Nat.digits b c).sum) [MOD d] :=
  Nat.ModEq.mul (Nat.modEq_digits_sum d b hb a) (Nat.modEq_digits_sum d b hb c)

-- Verification: casting out nines catches arithmetic errors
-- 123 × 456 = 56088. Digit sums: 6, 15, 27. 6 × 15 = 90 ≡ 0 (mod 9), 27 ≡ 0 (mod 9) ✓
example : 123 * 456 = 56088 := by native_decide
example : (Nat.digits 10 123).sum = 6 := by native_decide
example : (Nat.digits 10 456).sum = 15 := by native_decide
example : (Nat.digits 10 56088).sum = 27 := by native_decide

-- ============================================================
-- Part VI: Digital Root Theory
-- ============================================================

/-- Digital root: repeatedly sum digits until single digit.
    Computes n mod 9, except digitalRoot 0 = 0 and
    for n > 0 divisible by 9, digitalRoot n = 9. -/
def digitalRoot (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 9 = 0 then 9 else n % 9

/-- Digital root is always at most 9 -/
theorem digitalRoot_le_9 (n : ℕ) : digitalRoot n ≤ 9 := by
  unfold digitalRoot; split_ifs <;> omega

/-- Digital root of 0 is 0 -/
theorem digitalRoot_zero : digitalRoot 0 = 0 := by simp [digitalRoot]

/-- For nonzero n, digital root is positive -/
theorem digitalRoot_pos (n : ℕ) (hn : 0 < n) : 0 < digitalRoot n := by
  unfold digitalRoot; split_ifs <;> omega

/-- Digital root characterizes divisibility by 9 -/
theorem digitalRoot_eq_9_iff (n : ℕ) (hn : 0 < n) :
    digitalRoot n = 9 ↔ 9 ∣ n := by
  constructor
  · intro h
    unfold digitalRoot at h
    split_ifs at h with h1 h2 <;>
      first | exact Nat.dvd_of_mod_eq_zero h1 | exact Nat.dvd_of_mod_eq_zero h2 | omega
  · intro h9
    unfold digitalRoot
    have h2 : n % 9 = 0 := Nat.mod_eq_zero_of_dvd h9
    split_ifs with h1
    · omega
    · rfl

/-- Digital root mod 3 characterizes divisibility by 3 -/
theorem digitalRoot_mod3 (n : ℕ) : digitalRoot n % 3 = n % 3 := by
  unfold digitalRoot
  split_ifs with h1 h2
  · simp [h1]
  · omega
  · omega

/-- 3 divides n iff 3 divides its digital root -/
theorem three_dvd_iff_three_dvd_digitalRoot (n : ℕ) :
    3 ∣ n ↔ 3 ∣ digitalRoot n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, digitalRoot_mod3]

-- Digital root examples
example : digitalRoot 0 = 0 := by native_decide
example : digitalRoot 1 = 1 := by native_decide
example : digitalRoot 9 = 9 := by native_decide
example : digitalRoot 10 = 1 := by native_decide
example : digitalRoot 18 = 9 := by native_decide
example : digitalRoot 99 = 9 := by native_decide
example : digitalRoot 100 = 1 := by native_decide
example : digitalRoot 123 = 6 := by native_decide
example : digitalRoot 999 = 9 := by native_decide
example : digitalRoot 12345 = 6 := by native_decide

-- ============================================================
-- Part VII: Combined Rules (Coprime Factorization)
-- ============================================================

/-- **General coprime divisibility**: d₁ * d₂ | n ↔ d₁ | n ∧ d₂ | n -/
theorem coprime_mul_dvd_iff (d₁ d₂ n : ℕ) (h : Nat.Coprime d₁ d₂) :
    d₁ * d₂ ∣ n ↔ d₁ ∣ n ∧ d₂ ∣ n :=
  ⟨fun hd => ⟨dvd_trans (dvd_mul_right d₁ d₂) hd,
              dvd_trans (dvd_mul_left d₂ d₁) hd⟩,
   fun ⟨h₁, h₂⟩ => h.mul_dvd_of_dvd_of_dvd h₁ h₂⟩

/-- 6 | n ↔ 2 | n ∧ 3 | n -/
theorem six_dvd_iff (n : ℕ) : 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n :=
  coprime_mul_dvd_iff 2 3 n (by native_decide)

/-- 12 | n ↔ 4 | n ∧ 3 | n -/
theorem twelve_dvd_iff (n : ℕ) : 12 ∣ n ↔ 4 ∣ n ∧ 3 ∣ n :=
  coprime_mul_dvd_iff 4 3 n (by native_decide)

/-- 15 | n ↔ 3 | n ∧ 5 | n -/
theorem fifteen_dvd_iff (n : ℕ) : 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n :=
  coprime_mul_dvd_iff 3 5 n (by native_decide)

/-- 18 | n ↔ 2 | n ∧ 9 | n -/
theorem eighteen_dvd_iff (n : ℕ) : 18 ∣ n ↔ 2 ∣ n ∧ 9 ∣ n :=
  coprime_mul_dvd_iff 2 9 n (by native_decide)

/-- 36 | n ↔ 4 | n ∧ 9 | n -/
theorem thirtysix_dvd_iff (n : ℕ) : 36 ∣ n ↔ 4 ∣ n ∧ 9 ∣ n :=
  coprime_mul_dvd_iff 4 9 n (by native_decide)

/-- 45 | n ↔ 9 | n ∧ 5 | n -/
theorem fortyfive_dvd_iff (n : ℕ) : 45 ∣ n ↔ 9 ∣ n ∧ 5 ∣ n :=
  coprime_mul_dvd_iff 9 5 n (by native_decide)

/-- 60 | n ↔ 4 | n ∧ 15 | n -/
theorem sixty_dvd_iff (n : ℕ) : 60 ∣ n ↔ 4 ∣ n ∧ 15 ∣ n :=
  coprime_mul_dvd_iff 4 15 n (by native_decide)

/-- 90 | n ↔ 9 | n ∧ 10 | n -/
theorem ninety_dvd_iff (n : ℕ) : 90 ∣ n ↔ 9 ∣ n ∧ 10 ∣ n :=
  coprime_mul_dvd_iff 9 10 n (by native_decide)

-- ============================================================
-- Part VIII: Truncation Methods for 7 and 11
-- ============================================================

-- The truncation (osculator) method removes the last digit and adjusts by
-- a multiplier c. For p coprime to 10, if 10c ≡ 1 (mod p) (positive osculator)
-- then p | n ↔ p | (n/10 + c·(n%10)). If 10c ≡ -1 (mod p) (negative osculator)
-- then p | n ↔ p | (n/10 - c·(n%10)).

/-- **Divisibility by 7 truncation**: 7 | n ↔ 7 | (n/10 - 2·(n%10)).
    Proof: 10(q - 2r) = n - 21r, and 21 = 3·7. -/
theorem seven_dvd_truncation (n : ℕ) :
    7 ∣ n ↔ (7 : ℤ) ∣ (↑(n / 10) - 2 * ↑(n % 10)) := by
  constructor
  · intro ⟨k, hk⟩
    have key : (10 : ℤ) * (↑(n / 10) - 2 * ↑(n % 10)) = ↑n - 21 * ↑(n % 10) := by
      push_cast; omega
    have h21 : (7 : ℤ) ∣ (↑n - 21 * ↑(n % 10)) :=
      ⟨↑k - 3 * ↑(n % 10), by push_cast; omega⟩
    rw [← key] at h21
    exact IsCoprime.dvd_of_dvd_mul_left (by decide : IsCoprime (7 : ℤ) 10) h21
  · intro h7
    have key : (10 : ℤ) * (↑(n / 10) - 2 * ↑(n % 10)) = ↑n - 21 * ↑(n % 10) := by
      push_cast; omega
    have h10 : (7 : ℤ) ∣ (10 * (↑(n / 10) - 2 * ↑(n % 10))) :=
      dvd_mul_of_dvd_right h7 10
    rw [key] at h10
    have h21 : (7 : ℤ) ∣ (21 * ↑(n % 10)) := ⟨3 * ↑(n % 10), by ring⟩
    have hadd := Int.dvd_add h10 h21
    simp only [sub_add_cancel] at hadd
    exact_mod_cast hadd

/-- **Divisibility by 11 truncation**: 11 | n ↔ 11 | (n/10 - (n%10)).
    Proof: 10(q - r) = n - 11r. -/
theorem eleven_dvd_truncation (n : ℕ) :
    11 ∣ n ↔ (11 : ℤ) ∣ (↑(n / 10) - ↑(n % 10)) := by
  constructor
  · intro ⟨k, hk⟩
    have key : (10 : ℤ) * (↑(n / 10) - ↑(n % 10)) = ↑n - 11 * ↑(n % 10) := by
      push_cast; omega
    have h11 : (11 : ℤ) ∣ (↑n - 11 * ↑(n % 10)) :=
      ⟨↑k - ↑(n % 10), by push_cast; omega⟩
    rw [← key] at h11
    exact IsCoprime.dvd_of_dvd_mul_left (by decide : IsCoprime (11 : ℤ) 10) h11
  · intro h11
    have key : (10 : ℤ) * (↑(n / 10) - ↑(n % 10)) = ↑n - 11 * ↑(n % 10) := by
      push_cast; omega
    have h10 : (11 : ℤ) ∣ (10 * (↑(n / 10) - ↑(n % 10))) :=
      dvd_mul_of_dvd_right h11 10
    rw [key] at h10
    have h11m : (11 : ℤ) ∣ (11 * ↑(n % 10)) := ⟨↑(n % 10), by ring⟩
    have hadd := Int.dvd_add h10 h11m
    simp only [sub_add_cancel] at hadd
    exact_mod_cast hadd

-- Verification
example : 7 ∣ 49 := by native_decide
example : 7 ∣ 1001 := by native_decide
example : ¬(7 ∣ 100) := by native_decide
example : 11 ∣ 121 := by native_decide
example : 11 ∣ 1001 := by native_decide
example : ¬(11 ∣ 100) := by native_decide

-- ============================================================
-- Part IX: Truncation Methods for 17 and 19
-- ============================================================

/-- **Divisibility by 17 truncation**: 17 | n ↔ 17 | (n/10 - 5·(n%10)).
    Proof: 10(q - 5r) = n - 51r, and 51 = 3·17. -/
theorem seventeen_dvd_truncation (n : ℕ) :
    17 ∣ n ↔ (17 : ℤ) ∣ (↑(n / 10) - 5 * ↑(n % 10)) := by
  constructor
  · intro ⟨k, hk⟩
    have key : (10 : ℤ) * (↑(n / 10) - 5 * ↑(n % 10)) = ↑n - 51 * ↑(n % 10) := by
      push_cast; omega
    have h51 : (17 : ℤ) ∣ (↑n - 51 * ↑(n % 10)) :=
      ⟨↑k - 3 * ↑(n % 10), by push_cast; omega⟩
    rw [← key] at h51
    exact IsCoprime.dvd_of_dvd_mul_left (by decide : IsCoprime (17 : ℤ) 10) h51
  · intro h17
    have key : (10 : ℤ) * (↑(n / 10) - 5 * ↑(n % 10)) = ↑n - 51 * ↑(n % 10) := by
      push_cast; omega
    have h10 : (17 : ℤ) ∣ (10 * (↑(n / 10) - 5 * ↑(n % 10))) :=
      dvd_mul_of_dvd_right h17 10
    rw [key] at h10
    have h51 : (17 : ℤ) ∣ (51 * ↑(n % 10)) := ⟨3 * ↑(n % 10), by ring⟩
    have hadd := Int.dvd_add h10 h51
    simp only [sub_add_cancel] at hadd
    exact_mod_cast hadd

/-- **Divisibility by 19 truncation**: 19 | n ↔ 19 | (n/10 + 2·(n%10)).
    Proof: 10(q + 2r) = n + 19r. -/
theorem nineteen_dvd_truncation (n : ℕ) :
    19 ∣ n ↔ (19 : ℤ) ∣ (↑(n / 10) + 2 * ↑(n % 10)) := by
  constructor
  · intro ⟨k, hk⟩
    have key : (10 : ℤ) * (↑(n / 10) + 2 * ↑(n % 10)) = ↑n + 19 * ↑(n % 10) := by
      push_cast; omega
    have h19 : (19 : ℤ) ∣ (↑n + 19 * ↑(n % 10)) :=
      ⟨↑k + ↑(n % 10), by push_cast; omega⟩
    rw [← key] at h19
    exact IsCoprime.dvd_of_dvd_mul_left (by decide : IsCoprime (19 : ℤ) 10) h19
  · intro h19
    have key : (10 : ℤ) * (↑(n / 10) + 2 * ↑(n % 10)) = ↑n + 19 * ↑(n % 10) := by
      push_cast; omega
    have h10 : (19 : ℤ) ∣ (10 * (↑(n / 10) + 2 * ↑(n % 10))) :=
      dvd_mul_of_dvd_right h19 10
    rw [key] at h10
    have h19m : (19 : ℤ) ∣ (19 * ↑(n % 10)) := ⟨↑(n % 10), by ring⟩
    have hsub := Int.dvd_sub h10 h19m
    simp only [add_sub_cancel_right] at hsub
    exact_mod_cast hsub

-- Verification
example : 17 ∣ 51 := by native_decide
example : 17 ∣ 289 := by native_decide
example : ¬(17 ∣ 100) := by native_decide
example : 19 ∣ 57 := by native_decide
example : 19 ∣ 361 := by native_decide
example : ¬(19 ∣ 100) := by native_decide

-- ============================================================
-- Part X: Alternating Digit Grouping
-- ============================================================

-- 1001 = 7 × 11 × 13 means 1000 ≡ -1 (mod 7, 11, 13).
-- So alternating 3-digit group sums test divisibility by 7, 11, 13.
example : 1001 = 7 * 11 * 13 := by native_decide
example : 1000 % 7 = 6 := by native_decide
example : 1000 % 11 = 10 := by native_decide
example : 1000 % 13 = 12 := by native_decide

-- Osculator constants table (10c ≡ 1 mod p → positive, 10c ≡ -1 mod p → negative)
-- 7: neg c=2 (10·2=20, 20+1=21=3·7), pos c=5 (10·5=50, 50-1=49=7·7)
-- 11: neg c=1 (10·1=10, 10+1=11), pos c=10 (impractical)
-- 13: pos c=4 (10·4=40, 40-1=39=3·13), neg c=9
-- 17: neg c=5 (10·5=50, 50+1=51=3·17), pos c=12 (impractical)
-- 19: pos c=2 (10·2=20, 20-1=19), neg c=17 (impractical)
example : 10 * 5 % 7 = 1 := by native_decide
example : 10 * 4 % 13 = 1 := by native_decide
example : 10 * 2 % 19 = 1 := by native_decide

-- ============================================================
-- Part XI: Summary Theorem
-- ============================================================

/-- Master summary of divisibility rules proved in this extension -/
theorem divisibility_rules_summary :
    -- Digit sum rules (b ≡ 1 mod d)
    (∀ n, 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum) ∧
    (∀ n, 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum) ∧
    (∀ n, 37 ∣ n ↔ 37 ∣ (Nat.digits 1000 n).sum) ∧
    (∀ n, 99 ∣ n ↔ 99 ∣ (Nat.digits 100 n).sum) ∧
    -- Last-k-digit rules (d | b^k)
    (∀ n, 2 ∣ n ↔ 2 ∣ (n % 10)) ∧
    (∀ n, 4 ∣ n ↔ 4 ∣ (n % 100)) ∧
    (∀ n, 8 ∣ n ↔ 8 ∣ (n % 1000)) ∧
    (∀ n, 5 ∣ n ↔ 5 ∣ (n % 10)) ∧
    (∀ n, 25 ∣ n ↔ 25 ∣ (n % 100)) ∧
    -- Power generalizations
    (∀ k n, 2 ^ k ∣ n ↔ 2 ^ k ∣ (n % 10 ^ k)) ∧
    (∀ k n, 5 ^ k ∣ n ↔ 5 ^ k ∣ (n % 10 ^ k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => digitSum_dvd_iff 3 10 (by native_decide) n
  · exact fun n => digitSum_dvd_iff 9 10 (by native_decide) n
  · exact thirtyseven_dvd_base1000
  · exact ninetynine_dvd_base100
  · exact two_dvd_last1
  · exact four_dvd_last2
  · exact eight_dvd_last3
  · exact five_dvd_last1
  · exact twentyfive_dvd_last2
  · exact pow2_dvd_last_k
  · exact pow5_dvd_last_k

end DivisibilityByThreeOQ01
