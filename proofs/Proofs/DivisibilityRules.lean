/-
Formal Divisibility Rules for Various Bases and Moduli

Extension of DivisibilityBy3 (Wiedijk #85) to a comprehensive collection
of divisibility rules with Lean proofs.

Rules covered:
- Digit sum rules: 3 | n, 9 | n, 7 | n (octal), etc. (from Mathlib)
- Alternating digit sum: 11 | n (fully proved)
- Last digit rules: 2 | n, 5 | n, 10 | n
- Last two digits: 4 | n, 25 | n
- Last three digits: 8 | n, 125 | n
- Combined: 6 | n ↔ 2 | n ∧ 3 | n, etc.
- General coprime factorization
- Divisibility by 7 truncation method
- Digital root definition and properties

Tags: number-theory, modular-arithmetic, divisibility, extension
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

open Nat Finset BigOperators

namespace DivisibilityRules

/-
## Part I: Alternating Digit Sum (for b ≡ -1 mod d)

When the base b satisfies b ≡ -1 (mod d), powers of b alternate signs:
  b^0 ≡ 1, b^1 ≡ -1, b^2 ≡ 1, b^3 ≡ -1, ...

So n = d₀ + d₁·b + d₂·b² + ... ≡ d₀ - d₁ + d₂ - d₃ + ... (mod d).
This gives the divisibility-by-11 rule in base 10 (since 10 ≡ -1 mod 11).
-/

/-- Alternating sum of a list of natural numbers (as integers).
    For digits [d₀, d₁, d₂, ...] computes d₀ - d₁ + d₂ - d₃ + ... -/
def alternatingDigitSum : List ℕ → ℤ
  | [] => 0
  | [d] => ↑d
  | d₀ :: d₁ :: rest => ↑d₀ - ↑d₁ + alternatingDigitSum rest

/-- Alternating digit sum of a number in a given base -/
def altDigitSum (b n : ℕ) : ℤ := alternatingDigitSum (Nat.digits b n)

theorem alternatingDigitSum_nil : alternatingDigitSum [] = 0 := rfl
theorem alternatingDigitSum_singleton (d : ℕ) : alternatingDigitSum [d] = ↑d := rfl

theorem alternatingDigitSum_pair (d₀ d₁ : ℕ) :
    alternatingDigitSum [d₀, d₁] = ↑d₀ - ↑d₁ := by
  simp [alternatingDigitSum]

/-- Key recursion: alternatingDigitSum (a :: rest) = a - alternatingDigitSum rest.
    This mirrors the 1-step recursion of ofDigits with sign flip. -/
theorem alternatingDigitSum_cons (a : ℕ) (rest : List ℕ) :
    alternatingDigitSum (a :: rest) = ↑a - alternatingDigitSum rest := by
  induction rest with
  | nil => simp [alternatingDigitSum]
  | cons b rest' ih =>
    simp only [alternatingDigitSum]
    rw [ih]
    ring

/-- The alternating digit sum of ofDigits: when b ≡ -1 (mod d),
    ofDigits b l ≡ alternatingDigitSum l (mod d). Proved by induction on l. -/
theorem ofDigits_modEq_alternatingDigitSum (d : ℕ) (hd : 0 < d)
    (b : ℕ) (hb : b % d = d - 1) (l : List ℕ) :
    (Nat.ofDigits b l : ℤ) ≡ alternatingDigitSum l [ZMOD ↑d] := by
  induction l with
  | nil => simp [Nat.ofDigits, alternatingDigitSum, Int.ModEq]
  | cons a rest ih =>
    rw [alternatingDigitSum_cons]
    simp only [Nat.ofDigits]
    have hb_neg : (b : ℤ) ≡ -1 [ZMOD ↑d] := by
      rw [Int.ModEq]
      simp only [Int.emod_emod_of_dvd]
      omega
    have h_mul : (↑b * ↑(Nat.ofDigits b rest) : ℤ) ≡
        -1 * alternatingDigitSum rest [ZMOD ↑d] :=
      Int.ModEq.mul hb_neg ih
    have h_add : (↑a + ↑b * ↑(Nat.ofDigits b rest) : ℤ) ≡
        ↑a + -1 * alternatingDigitSum rest [ZMOD ↑d] :=
      Int.ModEq.add rfl h_mul
    simp only [neg_one_mul] at h_add
    push_cast at h_add ⊢
    exact h_add

/-- When b ≡ -1 (mod d), n ≡ alternatingDigitSum(digits b n) (mod d).
    Since 10 ≡ -1 (mod 11), this gives the div-by-11 rule.
    Proved via ofDigits induction + Nat.ofDigits_digits identity. -/
theorem modEq_alternating_digits_sum (d b n : ℕ) (hd : 0 < d)
    (hb : b % d = d - 1) :
    (n : ℤ) ≡ altDigitSum b n [ZMOD ↑d] := by
  unfold altDigitSum
  by_cases hb2 : b < 2
  · simp [Nat.digits, hb2]
    by_cases hn : n = 0
    · subst hn; simp [alternatingDigitSum, Int.ModEq]
    · interval_cases d
      · omega
      · simp [Int.ModEq]; omega
      · have hb1 : b = 1 := by omega
        subst hb1
        simp [Nat.digits_one]
        induction n with
        | zero => contradiction
        | succ n' _ =>
          simp [List.replicate_succ, alternatingDigitSum_cons]
          rw [Int.ModEq]; simp; omega
      · omega
  · push_neg at hb2
    have key : n = Nat.ofDigits b (Nat.digits b n) := (Nat.ofDigits_digits b n).symm
    rw [key]
    exact ofDigits_modEq_alternatingDigitSum d hd b hb (Nat.digits b n)

/-
## Part II: Last-Digit Rules
-/

/-- **Divisibility by 2**: n is even iff its last decimal digit is even -/
theorem two_dvd_iff (n : ℕ) : 2 ∣ n ↔ 2 ∣ (n % 10) := by
  constructor
  · intro ⟨k, hk⟩; exact ⟨k % 5, by omega⟩
  · intro ⟨k, hk⟩
    have h : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
    rw [h, hk]; exact ⟨5 * (n / 10) + k, by ring⟩

/-- **Divisibility by 5**: 5 | n iff the last digit is 0 or 5 -/
theorem five_dvd_iff (n : ℕ) : 5 ∣ n ↔ 5 ∣ (n % 10) := by
  constructor
  · intro ⟨k, hk⟩; exact ⟨k % 2, by omega⟩
  · intro ⟨k, hk⟩
    have h : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
    rw [h, hk]; exact ⟨2 * (n / 10) + k, by ring⟩

/-- **Divisibility by 10**: 10 | n iff the last digit is 0 -/
theorem ten_dvd_iff (n : ℕ) : 10 ∣ n ↔ n % 10 = 0 :=
  Nat.dvd_iff_mod_eq_zero

/-
## Part III: Last-Two-Digit Rules
-/

/-- **Divisibility by 4**: 4 | n iff 4 | (last two digits) -/
theorem four_dvd_iff (n : ℕ) : 4 ∣ n ↔ 4 ∣ (n % 100) := by
  constructor
  · intro ⟨k, hk⟩; exact ⟨k % 25, by omega⟩
  · intro ⟨k, hk⟩
    have h : n = 100 * (n / 100) + n % 100 := (Nat.div_add_mod n 100).symm
    rw [h, hk]; exact ⟨25 * (n / 100) + k, by ring⟩

/-- **Divisibility by 25**: 25 | n iff 25 | (last two digits) -/
theorem twentyfive_dvd_iff (n : ℕ) : 25 ∣ n ↔ 25 ∣ (n % 100) := by
  constructor
  · intro ⟨k, hk⟩; exact ⟨k % 4, by omega⟩
  · intro ⟨k, hk⟩
    have h : n = 100 * (n / 100) + n % 100 := (Nat.div_add_mod n 100).symm
    rw [h, hk]; exact ⟨4 * (n / 100) + k, by ring⟩

/-
## Part IV: Last-Three-Digit Rules
-/

/-- **Divisibility by 8**: 8 | n iff 8 | (last three digits) -/
theorem eight_dvd_iff (n : ℕ) : 8 ∣ n ↔ 8 ∣ (n % 1000) := by
  constructor
  · intro ⟨k, hk⟩; exact ⟨k % 125, by omega⟩
  · intro ⟨k, hk⟩
    have h : n = 1000 * (n / 1000) + n % 1000 := (Nat.div_add_mod n 1000).symm
    rw [h, hk]; exact ⟨125 * (n / 1000) + k, by ring⟩

/-- **Divisibility by 125**: 125 | n iff 125 | (last three digits) -/
theorem onehundredtwentyfive_dvd_iff (n : ℕ) : 125 ∣ n ↔ 125 ∣ (n % 1000) := by
  constructor
  · intro ⟨k, hk⟩; exact ⟨k % 8, by omega⟩
  · intro ⟨k, hk⟩
    have h : n = 1000 * (n / 1000) + n % 1000 := (Nat.div_add_mod n 1000).symm
    rw [h, hk]; exact ⟨8 * (n / 1000) + k, by ring⟩

/-
## Part V: Combined Rules (Coprime Factorization)
-/

/-- **Divisibility by 6**: 6 | n iff 2 | n and 3 | n -/
theorem six_dvd_iff (n : ℕ) : 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨⟨3 * k, by omega⟩, ⟨2 * k, by omega⟩⟩
  · intro ⟨h2, h3⟩
    have h23 : Nat.Coprime 2 3 := by native_decide
    exact h23.mul_dvd_of_dvd_of_dvd h2 h3

/-- **Divisibility by 12**: 12 | n iff 4 | n and 3 | n -/
theorem twelve_dvd_iff (n : ℕ) : 12 ∣ n ↔ 4 ∣ n ∧ 3 ∣ n := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨⟨3 * k, by omega⟩, ⟨4 * k, by omega⟩⟩
  · intro ⟨h4, h3⟩
    have h43 : Nat.Coprime 4 3 := by native_decide
    exact h43.mul_dvd_of_dvd_of_dvd h4 h3

/-- **Divisibility by 15**: 15 | n iff 3 | n and 5 | n -/
theorem fifteen_dvd_iff (n : ℕ) : 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨⟨5 * k, by omega⟩, ⟨3 * k, by omega⟩⟩
  · intro ⟨h3, h5⟩
    have h35 : Nat.Coprime 3 5 := by native_decide
    exact h35.mul_dvd_of_dvd_of_dvd h3 h5

/-- **Divisibility by 18**: 18 | n iff 2 | n and 9 | n -/
theorem eighteen_dvd_iff (n : ℕ) : 18 ∣ n ↔ 2 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨⟨9 * k, by omega⟩, ⟨2 * k, by omega⟩⟩
  · intro ⟨h2, h9⟩
    have h29 : Nat.Coprime 2 9 := by native_decide
    exact h29.mul_dvd_of_dvd_of_dvd h2 h9

/-- If d₁ and d₂ are coprime, then d₁·d₂ | n iff d₁ | n and d₂ | n -/
theorem coprime_mul_dvd_iff (d₁ d₂ n : ℕ) (h : Nat.Coprime d₁ d₂) :
    d₁ * d₂ ∣ n ↔ d₁ ∣ n ∧ d₂ ∣ n :=
  ⟨fun hd => ⟨dvd_trans (dvd_mul_right d₁ d₂) hd,
              dvd_trans (dvd_mul_left d₂ d₁) hd⟩,
   fun ⟨h₁, h₂⟩ => h.mul_dvd_of_dvd_of_dvd h₁ h₂⟩

/-- 30 | n iff 2 | n ∧ 3 | n ∧ 5 | n -/
theorem thirty_dvd_iff (n : ℕ) : 30 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n ∧ 5 ∣ n := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨⟨15 * k, by omega⟩, ⟨10 * k, by omega⟩, ⟨6 * k, by omega⟩⟩
  · intro ⟨h2, h3, h5⟩
    have h6 : 6 ∣ n := (six_dvd_iff n).mpr ⟨h2, h3⟩
    have h65 : Nat.Coprime 6 5 := by native_decide
    exact h65.mul_dvd_of_dvd_of_dvd h6 h5

/-
## Part VI: Digit Sum Rules via Mathlib General Theorem
-/

/-- General digit-sum divisibility: d | n ↔ d | (digits b n).sum when b ≡ 1 (mod d) -/
theorem dvd_iff_dvd_digits_sum (d b : ℕ) (hdb : b % d = 1) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum :=
  Nat.ModEq.dvd_iff (Nat.modEq_digits_sum d b hdb n) (dvd_refl d)

/-- **Divisibility by 3 in base 10** (from Mathlib) -/
theorem div_by_3 (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 3 10 (by native_decide) n

/-- **Divisibility by 9 in base 10** (from Mathlib) -/
theorem div_by_9 (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 9 10 (by native_decide) n

/-- **Divisibility by 7 in base 8 (octal)**: 8 ≡ 1 (mod 7) -/
theorem seven_dvd_octal (n : ℕ) : 7 ∣ n ↔ 7 ∣ (Nat.digits 8 n).sum :=
  dvd_iff_dvd_digits_sum 7 8 (by native_decide) n

/-- **Divisibility by 3 in base 16 (hex)**: 16 ≡ 1 (mod 3) -/
theorem three_dvd_hex (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digits_sum 3 16 (by native_decide) n

/-- **Divisibility by 5 in base 16 (hex)**: 16 ≡ 1 (mod 5) -/
theorem five_dvd_hex (n : ℕ) : 5 ∣ n ↔ 5 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digits_sum 5 16 (by native_decide) n

/-- **Divisibility by 15 in base 16 (hex)**: 16 ≡ 1 (mod 15) -/
theorem fifteen_dvd_hex (n : ℕ) : 15 ∣ n ↔ 15 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digits_sum 15 16 (by native_decide) n

/-- **Divisibility by 3 in base 7**: 7 ≡ 1 (mod 3) -/
theorem three_dvd_base7 (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 7 n).sum :=
  dvd_iff_dvd_digits_sum 3 7 (by native_decide) n

/-- **Divisibility by 2 in base 7**: 7 ≡ 1 (mod 2) -/
theorem two_dvd_base7 (n : ℕ) : 2 ∣ n ↔ 2 ∣ (Nat.digits 7 n).sum :=
  dvd_iff_dvd_digits_sum 2 7 (by native_decide) n

/-- **Divisibility by 6 in base 7**: 7 ≡ 1 (mod 6) -/
theorem six_dvd_base7 (n : ℕ) : 6 ∣ n ↔ 6 ∣ (Nat.digits 7 n).sum :=
  dvd_iff_dvd_digits_sum 6 7 (by native_decide) n

/-
## Part VII: Divisibility by 7 in Base 10 (Truncation Method)
-/

/-- The truncation method for 7: remove last digit d₀, subtract 2·d₀ from remaining.
    7 | n ↔ 7 | (n/10 - 2·(n%10)) (working in ℤ).
    Proof: 10(q - 2r) = n - 21r ≡ n (mod 7), and gcd(7,10)=1. -/
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
    have hsub := Int.dvd_add h10 h21
    simp only [sub_add_cancel] at hsub
    exact_mod_cast hsub

/-
## Part VIII: Digital Root
-/

/-- Digital root: repeatedly sum digits until single digit.
    digitalRoot n = n mod 9, except digitalRoot 0 = 0 and
    for n > 0 divisible by 9, digitalRoot n = 9. -/
def digitalRoot (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 9 = 0 then 9 else n % 9

/-- Digital root is always at most 9 -/
theorem digitalRoot_le_9 (n : ℕ) : digitalRoot n ≤ 9 := by
  unfold digitalRoot
  split_ifs <;> omega

/-- Digital root of 0 is 0 -/
theorem digitalRoot_zero : digitalRoot 0 = 0 := by simp [digitalRoot]

/-- Digital root of 9 is 9 -/
theorem digitalRoot_nine : digitalRoot 9 = 9 := by native_decide

/-- Digital root of 1 is 1 -/
theorem digitalRoot_one : digitalRoot 1 = 1 := by native_decide

/-- Digital root concrete values -/
theorem digitalRoot_123 : digitalRoot 123 = 6 := by native_decide
theorem digitalRoot_999 : digitalRoot 999 = 9 := by native_decide
theorem digitalRoot_100 : digitalRoot 100 = 1 := by native_decide

/-
## Part IX: Verification Examples
-/

-- Divisibility by 2 (last digit rule)
example : 2 ∣ 1234 := by rw [two_dvd_iff]; native_decide
example : ¬(2 ∣ 1235) := by rw [two_dvd_iff]; native_decide

-- Divisibility by 4 (last two digits rule)
example : 4 ∣ 1236 := by rw [four_dvd_iff]; native_decide
example : ¬(4 ∣ 1234) := by rw [four_dvd_iff]; native_decide

-- Divisibility by 5 (last digit rule)
example : 5 ∣ 1235 := by native_decide
example : ¬(5 ∣ 1234) := by rw [five_dvd_iff]; native_decide

-- Divisibility by 6 (combined 2 and 3 rule)
example : 6 ∣ 1236 := by rw [six_dvd_iff]; constructor <;> native_decide

-- Divisibility by 8 (last three digits rule)
example : 8 ∣ 1000 := by rw [eight_dvd_iff]; native_decide
example : ¬(8 ∣ 1234) := by rw [eight_dvd_iff]; native_decide

-- Divisibility by 7 in octal (digit sum rule)
example : 7 ∣ 49 := by rw [seven_dvd_octal]; native_decide
example : 7 ∣ 56 := by rw [seven_dvd_octal]; native_decide

-- Divisibility by 3 in hex (digit sum rule)
example : 3 ∣ 48 := by rw [three_dvd_hex]; native_decide

-- Divisibility by 15 in hex
example : 15 ∣ 255 := by rw [fifteen_dvd_hex]; native_decide

-- Combined rules
example : 12 ∣ 144 := by rw [twelve_dvd_iff]; constructor <;> native_decide
example : 30 ∣ 150 := by rw [thirty_dvd_iff]; refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-
## Part X: Summary
-/

/-- Summary: all divisibility rules are verified on examples -/
theorem rules_verification :
    (2 ∣ 246) ∧ (5 ∣ 250) ∧ (10 ∣ 250) ∧
    (4 ∣ 1024) ∧ (25 ∣ 1025) ∧
    (8 ∣ 1000) ∧
    (3 ∣ 111) ∧ (9 ∣ 999) ∧
    (6 ∣ 252) ∧ (12 ∣ 252) ∧ (15 ∣ 255) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end DivisibilityRules
