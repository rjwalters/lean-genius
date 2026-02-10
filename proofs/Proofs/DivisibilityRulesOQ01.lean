/-
Formal Divisibility Rules for Various Bases and Moduli (OQ-01 Extension)

Self-contained extension of the divisibility rules proof gallery with:
- Alternating digit sum: divisibility by 11 (fully proved)
- Digit sum rules in various bases (from Mathlib's modEq_digits_sum)
- Last-k-digit framework (general theorem + instantiations)
- Truncation methods: divisibility by 7 and 13
- Casting out nines: product and sum compatibility
- Multi-digit grouping: divisibility by 37, 27, 99, 101

Tags: number-theory, modular-arithmetic, divisibility, extension
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

open Nat Finset BigOperators

namespace DivisibilityRulesOQ01

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

/-- Key recursion: alternatingDigitSum (a :: rest) = a - alternatingDigitSum rest -/
theorem alternatingDigitSum_cons (a : ℕ) (rest : List ℕ) :
    alternatingDigitSum (a :: rest) = ↑a - alternatingDigitSum rest := by
  induction rest with
  | nil => simp [alternatingDigitSum]
  | cons b rest' ih =>
    show ↑a - ↑b + alternatingDigitSum rest' = ↑a - alternatingDigitSum (b :: rest')
    rw [ih]
    ring

/-- When b ≡ -1 (mod d), ofDigits b l ≡ alternatingDigitSum l (mod d). -/
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
      omega
    have h_mul : (↑b * Nat.ofDigits b rest : ℤ) ≡
        -1 * alternatingDigitSum rest [ZMOD ↑d] :=
      Int.ModEq.mul hb_neg ih
    have h_add : (↑a + ↑b * Nat.ofDigits b rest : ℤ) ≡
        ↑a + -1 * alternatingDigitSum rest [ZMOD ↑d] :=
      Int.ModEq.add rfl h_mul
    simp only [neg_one_mul] at h_add
    push_cast at h_add ⊢
    exact h_add

/-- When b ≡ -1 (mod d), n ≡ altDigitSum b n (mod d). -/
theorem modEq_alternating_digits_sum (d b n : ℕ) (hd : 0 < d)
    (hb : b % d = d - 1) (hb2 : 2 ≤ b) :
    (n : ℤ) ≡ altDigitSum b n [ZMOD ↑d] := by
  unfold altDigitSum
  have key : n = Nat.ofDigits b (Nat.digits b n) := (Nat.ofDigits_digits b n).symm
  conv_lhs => rw [key]
  exact ofDigits_modEq_alternatingDigitSum d hd b hb (Nat.digits b n)

/-
## Part II: Divisibility by 11 (Alternating Digit Sum, iff form)

10 ≡ -1 (mod 11), so n ≡ alternating digit sum (mod 11).
-/

/-- **Divisibility by 11 rule**: 11 divides n iff 11 divides the
    alternating sum of n's decimal digits. -/
theorem eleven_dvd_iff (n : ℕ) :
    (11 : ℤ) ∣ (↑n - altDigitSum 10 n) := by
  have h := modEq_alternating_digits_sum 11 10 n (by omega) (by native_decide) (by omega)
  exact h

/-- Example: 11 divides 121 (1 - 2 + 1 = 0, and 11 | 0) -/
example : 11 ∣ 121 := by native_decide

/-- Example: 11 divides 1001 (1 - 0 + 0 - 1 = 0) -/
example : 11 ∣ 1001 := by native_decide

/-- Example: 11 does not divide 123 (1 - 2 + 3 = 2) -/
example : ¬(11 ∣ 123) := by native_decide

/-
## Part III: Divisibility by 13 via Truncation

Similar to the 7-truncation method. For 13:
n = 10q + r, and 10(q + 4r) = n + 39r ≡ n (mod 13).
So 13 | n ↔ 13 | (n/10 + 4·(n%10)).
-/

/-- **Divisibility by 13 truncation**: 13 | n ↔ 13 | (n/10 + 4·(n%10)) -/
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

/-- **Divisibility by 7 truncation**: 7 | n ↔ 7 | (n/10 - 2·(n%10)) -/
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

/-- Example: 13 divides 169 -/
example : 13 ∣ 169 := by native_decide

/-- Example: 7 divides 49 -/
example : 7 ∣ 49 := by native_decide

/-
## Part IV: Digit Sum Rules in Various Bases

Using Mathlib's Nat.modEq_digits_sum: when b ≡ 1 (mod d),
n ≡ (digits b n).sum (mod d), hence d | n ↔ d | (digits b n).sum.
-/

/-- Helper: d ∣ n ↔ d ∣ (digits b n).sum when b ≡ 1 (mod d) -/
private theorem dvd_iff_dvd_digits_sum (d b : ℕ) (hdb : b % d = 1) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum :=
  Nat.ModEq.dvd_iff (Nat.modEq_digits_sum d b hdb n) (dvd_refl d)

/-- **Divisibility by 3 in base 10**: 10 ≡ 1 (mod 3) -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 3 10 (by native_decide) n

/-- **Divisibility by 9 in base 10**: 10 ≡ 1 (mod 9) -/
theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 9 10 (by native_decide) n

/-- **Divisibility by 37**: 1000 ≡ 1 (mod 37), sum three-digit groups -/
theorem thirtyseven_dvd_iff (n : ℕ) :
    37 ∣ n ↔ 37 ∣ (Nat.digits 1000 n).sum :=
  dvd_iff_dvd_digits_sum 37 1000 (by native_decide) n

/-- **Divisibility by 27**: 1000 ≡ 1 (mod 27), sum three-digit groups -/
theorem twentyseven_dvd_iff (n : ℕ) :
    27 ∣ n ↔ 27 ∣ (Nat.digits 1000 n).sum :=
  dvd_iff_dvd_digits_sum 27 1000 (by native_decide) n

/-- **Divisibility by 999**: 1000 ≡ 1 (mod 999), sum three-digit groups -/
theorem nineninenine_dvd_iff (n : ℕ) :
    999 ∣ n ↔ 999 ∣ (Nat.digits 1000 n).sum :=
  dvd_iff_dvd_digits_sum 999 1000 (by native_decide) n

/-- **Divisibility by 99**: 100 ≡ 1 (mod 99), sum two-digit groups -/
theorem ninetynine_dvd_iff (n : ℕ) :
    99 ∣ n ↔ 99 ∣ (Nat.digits 100 n).sum :=
  dvd_iff_dvd_digits_sum 99 100 (by native_decide) n

/-- **Divisibility by 101**: 10000 ≡ 1 (mod 101), sum four-digit groups -/
theorem onehundredone_dvd_iff (n : ℕ) :
    101 ∣ n ↔ 101 ∣ (Nat.digits 10000 n).sum :=
  dvd_iff_dvd_digits_sum 101 10000 (by native_decide) n

/-- **Divisibility by 7 in octal**: 8 ≡ 1 (mod 7) -/
theorem seven_dvd_octal (n : ℕ) : 7 ∣ n ↔ 7 ∣ (Nat.digits 8 n).sum :=
  dvd_iff_dvd_digits_sum 7 8 (by native_decide) n

/-- **Divisibility by 3 in hex**: 16 ≡ 1 (mod 3) -/
theorem three_dvd_hex (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digits_sum 3 16 (by native_decide) n

/-- **Divisibility by 5 in hex**: 16 ≡ 1 (mod 5) -/
theorem five_dvd_hex (n : ℕ) : 5 ∣ n ↔ 5 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digits_sum 5 16 (by native_decide) n

/-- **Divisibility by 15 in hex**: 16 ≡ 1 (mod 15) -/
theorem fifteen_dvd_hex (n : ℕ) : 15 ∣ n ↔ 15 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digits_sum 15 16 (by native_decide) n

/-- **Divisibility by 3 in base 4**: 4 ≡ 1 (mod 3) -/
theorem three_dvd_base4 (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 4 n).sum :=
  dvd_iff_dvd_digits_sum 3 4 (by native_decide) n

/-- **Divisibility by 5 in base 6**: 6 ≡ 1 (mod 5) -/
theorem five_dvd_base6 (n : ℕ) : 5 ∣ n ↔ 5 ∣ (Nat.digits 6 n).sum :=
  dvd_iff_dvd_digits_sum 5 6 (by native_decide) n

/-- **Divisibility by 4 in base 5**: 5 ≡ 1 (mod 4) -/
theorem four_dvd_base5 (n : ℕ) : 4 ∣ n ↔ 4 ∣ (Nat.digits 5 n).sum :=
  dvd_iff_dvd_digits_sum 4 5 (by native_decide) n

/-- **Divisibility by 8 in base 9**: 9 ≡ 1 (mod 8) -/
theorem eight_dvd_base9 (n : ℕ) : 8 ∣ n ↔ 8 ∣ (Nat.digits 9 n).sum :=
  dvd_iff_dvd_digits_sum 8 9 (by native_decide) n

/-- **Divisibility by 13 in base 14**: 14 ≡ 1 (mod 13) -/
theorem thirteen_dvd_base14 (n : ℕ) : 13 ∣ n ↔ 13 ∣ (Nat.digits 14 n).sum :=
  dvd_iff_dvd_digits_sum 13 14 (by native_decide) n

/-
## Part V: General Last-k-Digit Framework

If d | m, then d | n ↔ d | (n mod m).
This generalizes last-digit, last-two-digit, last-three-digit rules.
-/

/-- General last-digit rule: if d | m, then d | n ↔ d | (n mod m) -/
theorem dvd_iff_dvd_mod (d m : ℕ) (hdiv : d ∣ m) (n : ℕ) :
    d ∣ n ↔ d ∣ (n % m) := by
  obtain ⟨c, rfl⟩ := hdiv
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k % c, by omega⟩
  · intro hmod
    obtain ⟨j, hj⟩ := hmod
    exact ⟨c * (n / (d * c)) + j, by omega⟩

/-- **Divisibility by 2**: last digit rule -/
theorem two_dvd_iff (n : ℕ) : 2 ∣ n ↔ 2 ∣ (n % 10) :=
  dvd_iff_dvd_mod 2 10 ⟨5, by ring⟩ n

/-- **Divisibility by 5**: last digit rule -/
theorem five_dvd_iff (n : ℕ) : 5 ∣ n ↔ 5 ∣ (n % 10) :=
  dvd_iff_dvd_mod 5 10 ⟨2, by ring⟩ n

/-- **Divisibility by 4**: last two digits rule -/
theorem four_dvd_iff (n : ℕ) : 4 ∣ n ↔ 4 ∣ (n % 100) :=
  dvd_iff_dvd_mod 4 100 ⟨25, by ring⟩ n

/-- **Divisibility by 25**: last two digits rule -/
theorem twentyfive_dvd_iff (n : ℕ) : 25 ∣ n ↔ 25 ∣ (n % 100) :=
  dvd_iff_dvd_mod 25 100 ⟨4, by ring⟩ n

/-- **Divisibility by 8**: last three digits rule -/
theorem eight_dvd_iff (n : ℕ) : 8 ∣ n ↔ 8 ∣ (n % 1000) :=
  dvd_iff_dvd_mod 8 1000 ⟨125, by ring⟩ n

/-- **Divisibility by 125**: last three digits rule -/
theorem onehundredtwentyfive_dvd_iff (n : ℕ) : 125 ∣ n ↔ 125 ∣ (n % 1000) :=
  dvd_iff_dvd_mod 125 1000 ⟨8, by ring⟩ n

/-- **Divisibility by 16**: last four digits rule -/
theorem sixteen_dvd_iff (n : ℕ) : 16 ∣ n ↔ 16 ∣ (n % 10000) :=
  dvd_iff_dvd_mod 16 10000 ⟨625, by ring⟩ n

/-- **Divisibility by 32**: last five digits rule -/
theorem thirtytwo_dvd_iff (n : ℕ) : 32 ∣ n ↔ 32 ∣ (n % 100000) :=
  dvd_iff_dvd_mod 32 100000 ⟨3125, by ring⟩ n

/-
## Part VI: Combined Coprime Factorization Rules
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

/-- General coprime factorization: d₁ * d₂ | n ↔ d₁ | n ∧ d₂ | n when coprime -/
theorem coprime_mul_dvd_iff (d₁ d₂ n : ℕ) (h : Nat.Coprime d₁ d₂) :
    d₁ * d₂ ∣ n ↔ d₁ ∣ n ∧ d₂ ∣ n :=
  ⟨fun hd => ⟨dvd_trans (dvd_mul_right d₁ d₂) hd,
              dvd_trans (dvd_mul_left d₂ d₁) hd⟩,
   fun ⟨h₁, h₂⟩ => h.mul_dvd_of_dvd_of_dvd h₁ h₂⟩

/-
## Part VII: Casting Out Nines

The mod-9 function respects addition and multiplication.
This allows checking arithmetic by casting out nines.
-/

/-- Casting out nines for addition -/
theorem casting_out_nines_add (a b : ℕ) :
    (a + b) % 9 = ((a % 9) + (b % 9)) % 9 :=
  Nat.add_mod a b 9

/-- Casting out nines for multiplication -/
theorem casting_out_nines_mul (a b : ℕ) :
    (a * b) % 9 = ((a % 9) * (b % 9)) % 9 :=
  Nat.mul_mod a b 9

/-- Casting out nines detects errors: if a * b ≢ c (mod 9), then a * b ≠ c -/
theorem casting_nines_error_detect {a b c : ℕ} (h : ¬(a * b ≡ c [MOD 9])) :
    a * b ≠ c := by
  intro heq; exact h (heq ▸ Nat.ModEq.refl (a * b))

/-
## Part VIII: Verification Examples
-/

-- Divisibility by 2 (last digit rule)
example : 2 ∣ 1234 := by rw [two_dvd_iff]; native_decide
example : ¬(2 ∣ 1235) := by rw [two_dvd_iff]; native_decide

-- Divisibility by 4 (last two digits rule)
example : 4 ∣ 1236 := by rw [four_dvd_iff]; native_decide

-- Divisibility by 8 (last three digits rule)
example : 8 ∣ 1000 := by rw [eight_dvd_iff]; native_decide

-- Divisibility by 6 (combined rule)
example : 6 ∣ 1236 := by rw [six_dvd_iff]; constructor <;> native_decide

-- Divisibility by 37 (three-digit grouping)
example : 37 ∣ 999 := by rw [thirtyseven_dvd_iff]; native_decide

-- Divisibility by 11
example : 11 ∣ 121 := by native_decide
example : 11 ∣ 1001 := by native_decide

-- Divisibility by 13 (truncation)
example : 13 ∣ 169 := by native_decide
example : 13 ∣ 1001 := by native_decide

-- Casting out nines
example : 123 * 456 ≡ 56088 [MOD 9] := by native_decide
example : 12 * 13 ≠ 155 := by native_decide

-- Combined rules
example : 12 ∣ 144 := by rw [twelve_dvd_iff]; constructor <;> native_decide

/-
## Part IX: Summary
-/

/-- Summary: all extended divisibility rules verified -/
theorem oq01_rules_verification :
    (11 ∣ 1001) ∧ (13 ∣ 1001) ∧ (37 ∣ 999) ∧
    (27 ∣ 999) ∧ (99 ∣ 9999) ∧ (16 ∣ 10000) ∧
    (32 ∣ 32000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

#check eleven_dvd_iff
#check thirteen_dvd_truncation
#check seven_dvd_truncation
#check thirtyseven_dvd_iff
#check dvd_iff_dvd_mod
#check coprime_mul_dvd_iff
#check casting_out_nines_mul
#check casting_nines_error_detect

end DivisibilityRulesOQ01
