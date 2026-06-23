import Mathlib

/-
# The Alternating Digit-Sum Rule for b+1 (OQ-02-OQ-01)

## What This Proves
The companion of the base-b digit-sum rule. The parent OQ-02 file establishes the
"sum of digits" test for `b - 1` (because `b ≡ 1 (mod b-1)`).  Here we establish the
**alternating** sum of digits test for `b + 1`:

  For every base `b` and every `n`,
      n ≡ alternatingSum(digits b n)   (mod b+1),
  hence
      (b+1) ∣ n   ↔   (b+1) ∣ alternatingSum(digits b n).

This is the universal principle behind the classical "divisibility by 11" test in
base 10 (alternate adding and subtracting digits), and it works in *every* base:
  * base 10 → divisibility by **11**  (recovers `Nat.eleven_dvd_iff`)
  * base  2 → divisibility by **3**   (alternating bit sum)
  * base  8 → divisibility by **9**
  * base 16 → divisibility by **17**
  * base 12 → divisibility by **13**, etc.

## Key Mathematical Insight
Since `b ≡ -1 (mod b+1)`, every power `b^k ≡ (-1)^k (mod b+1)`.  Therefore

  n = ∑ dᵢ · bⁱ  ≡  ∑ dᵢ · (-1)ⁱ  =  alternating digit sum   (mod b+1).

The alternating sum is taken in `ℤ` (it can be negative), so the congruences are
stated with `[ZMOD (b+1)]` and `(b+1 : ℤ) ∣ …`.

## Relation to Mathlib
Mathlib proves the **base-10 specialization** only:
  `Nat.modEq_eleven_digits_sum` and `Nat.eleven_dvd_iff` (theorem #85 of Freek's list).
Both go through the generic facts
  `Nat.zmodeq_ofDigits_digits`, `Nat.dvd_iff_dvd_ofDigits`, `Nat.ofDigits_neg_one`.
We promote those generic facts to the full base-`b → (b+1)` family — the content the
OQ asks for — and recover the base-10 rule as a corollary, plus new instances in other
bases that Mathlib does not provide.

## Status
- [x] `b ≡ -1 (mod b+1)` (the driving congruence)
- [x] General congruence  n ≡ alternatingSum [ZMOD b+1]
- [x] General divisibility iff  (b+1) ∣ n ↔ (b+1) ∣ alternatingSum
- [x] Recovers Mathlib's base-10 `eleven_dvd_iff`
- [x] New base instances: binary→3, octal→9, hex→17, duodecimal→13
- [x] Even-length palindrome ⟹ (b+1) ∣ n (generalizes `eleven_dvd_of_palindrome`)
- [x] Numerical verifications
-/

namespace DivisibilityBy3OQ02OQ01

open Nat

/-- Convenience notation: the alternating sum of the base-`b` digits of `n`, taken in `ℤ`.
    `altDigitSum b n = d₀ - d₁ + d₂ - d₃ + …` where `digits b n = [d₀, d₁, d₂, …]`. -/
def altDigitSum (b n : ℕ) : ℤ :=
  ((Nat.digits b n).map (fun k : ℕ => (k : ℤ))).alternatingSum

-- ============================================================
-- Part I: The Driving Congruence  b ≡ -1 (mod b+1)
-- ============================================================

/-- The base is congruent to `-1` modulo `b+1`. This is what makes alternating sums work:
    `b ≡ -1` forces `b^k ≡ (-1)^k`. -/
theorem base_zmodEq_neg_one (b : ℕ) : (b : ℤ) ≡ -1 [ZMOD (b + 1 : ℕ)] := by
  -- `b ≡ -1 [ZMOD b+1]`  ↔  `(b+1) ∣ (-1 - b)`  and  `-1 - b = (b+1)·(-1)`.
  rw [Int.modEq_iff_dvd]
  push_cast
  exact ⟨-1, by ring⟩

-- ============================================================
-- Part II: The General Alternating Digit-Sum Congruence
-- ============================================================

/-- **The (b+1) congruence.** In any base `b`, a number is congruent to the alternating
    sum of its base-`b` digits modulo `b + 1`. -/
theorem modEq_altDigitSum (b n : ℕ) :
    (n : ℤ) ≡ altDigitSum b n [ZMOD (b + 1 : ℕ)] := by
  have t := Nat.zmodeq_ofDigits_digits (b + 1) b (-1 : ℤ) (base_zmodEq_neg_one b) n
  rwa [Nat.ofDigits_neg_one] at t

/-- The alternating sum determines the residue of `n` modulo `b + 1`
    (an `Int.emod` reformulation of `modEq_altDigitSum`). -/
theorem emod_altDigitSum (b n : ℕ) :
    (n : ℤ) % (b + 1 : ℕ) = altDigitSum b n % (b + 1 : ℕ) :=
  modEq_altDigitSum b n

-- ============================================================
-- Part III: The General Divisibility Rule
-- ============================================================

/-- **The (b+1) divisibility rule.** In any base `b`, `b + 1` divides `n` iff `b + 1`
    divides the alternating sum of the base-`b` digits of `n`. -/
theorem succ_dvd_iff_altDigitSum (b n : ℕ) :
    (b + 1) ∣ n ↔ ((b + 1 : ℕ) : ℤ) ∣ altDigitSum b n := by
  have t := Nat.dvd_iff_dvd_ofDigits (b + 1) b (-1 : ℤ)
    (by push_cast; exact ⟨1, by ring⟩) n
  rwa [Nat.ofDigits_neg_one] at t

/-- The same rule with the modulus written directly over `ℤ`. -/
theorem succ_dvd_iff_altDigitSum' (b n : ℕ) :
    (b + 1) ∣ n ↔ ((b : ℤ) + 1) ∣ altDigitSum b n := by
  rw [succ_dvd_iff_altDigitSum]; push_cast; rfl

-- ============================================================
-- Part IV: Recovering Mathlib's Base-10 Rule (Consistency)
-- ============================================================

/-- Base 10 specialization of the congruence — definitionally Mathlib's
    `Nat.modEq_eleven_digits_sum`. -/
theorem modEq_eleven (n : ℕ) :
    (n : ℤ) ≡ ((Nat.digits 10 n).map (fun k : ℕ => (k : ℤ))).alternatingSum [ZMOD 11] :=
  modEq_altDigitSum 10 n

/-- Base 10 specialization of the divisibility rule: this is Mathlib's
    `Nat.eleven_dvd_iff`, recovered from the general theorem. -/
theorem eleven_dvd_iff (n : ℕ) :
    11 ∣ n ↔ (11 : ℤ) ∣ ((Nat.digits 10 n).map (fun k : ℕ => (k : ℤ))).alternatingSum :=
  succ_dvd_iff_altDigitSum 10 n

-- ============================================================
-- Part V: New Base Instances (not in Mathlib)
-- ============================================================

/-- **Binary → 3**: `3 ∣ n` iff `3` divides the alternating sum of the *bits* of `n`. -/
theorem three_dvd_iff_binary (n : ℕ) :
    3 ∣ n ↔ (3 : ℤ) ∣ altDigitSum 2 n :=
  succ_dvd_iff_altDigitSum 2 n

/-- **Octal → 9**: `9 ∣ n` iff `9` divides the alternating sum of the base-8 digits. -/
theorem nine_dvd_iff_octal (n : ℕ) :
    9 ∣ n ↔ (9 : ℤ) ∣ altDigitSum 8 n :=
  succ_dvd_iff_altDigitSum 8 n

/-- **Hexadecimal → 17**: `17 ∣ n` iff `17` divides the alternating sum of the hex digits. -/
theorem seventeen_dvd_iff_hex (n : ℕ) :
    17 ∣ n ↔ (17 : ℤ) ∣ altDigitSum 16 n :=
  succ_dvd_iff_altDigitSum 16 n

/-- **Duodecimal → 13**: `13 ∣ n` iff `13` divides the alternating sum of the base-12 digits. -/
theorem thirteen_dvd_iff_duodecimal (n : ℕ) :
    13 ∣ n ↔ (13 : ℤ) ∣ altDigitSum 12 n :=
  succ_dvd_iff_altDigitSum 12 n

-- ============================================================
-- Part VI: Even-Length Palindromes
-- ============================================================

/-- **Even-length palindromes are divisible by b+1.** If the base-`b` digit list of `n`
    is a palindrome of even length, then `(b+1) ∣ n`. Generalizes Mathlib's
    `Nat.eleven_dvd_of_palindrome` (the base-10 case) to every base. -/
theorem succ_dvd_of_palindrome {b n : ℕ}
    (p : (Nat.digits b n).Palindrome) (h : Even (Nat.digits b n).length) :
    (b + 1) ∣ n := by
  let dig := (Nat.digits b n).map (fun k : ℕ => (k : ℤ))
  have hlen : Even dig.length := by rwa [List.length_map]
  rw [succ_dvd_iff_altDigitSum]
  refine ⟨0, (?_ : altDigitSum b n = 0)⟩
  have hrev := dig.alternatingSum_reverse
  rw [(p.map _).reverse_eq, _root_.pow_succ', hlen.neg_one_pow, mul_one, neg_one_zsmul] at hrev
  exact eq_zero_of_neg_eq hrev.symm

-- ============================================================
-- Part VII: Numerical Verifications
-- ============================================================

/-- `121 = 11²`, base-10 digits `[1,2,1]`, alternating sum `1 - 2 + 1 = 0`, so `11 ∣ 121`. -/
example : 11 ∣ 121 := by rw [eleven_dvd_iff]; native_decide

/-- `132 = 11·12`, alternating digit sum `2 - 3 + 1 = 0`, so `11 ∣ 132`. -/
example : 11 ∣ 132 := by rw [eleven_dvd_iff]; native_decide

/-- `123` is **not** divisible by 11 (alternating sum `3 - 2 + 1 = 2`). -/
example : ¬ (11 ∣ 123) := by rw [eleven_dvd_iff]; native_decide

/-- Binary check: `9 = 0b1001`, bits `[1,0,0,1]`, alternating sum `1 - 0 + 0 - 1 = 0`,
    so `3 ∣ 9`. -/
example : 3 ∣ 9 := by rw [three_dvd_iff_binary]; native_decide

/-- Hex check: `17 = 0x11`, hex digits `[1,1]`, alternating sum `1 - 1 = 0`, so `17 ∣ 17`. -/
example : 17 ∣ 17 := by rw [seventeen_dvd_iff_hex]; native_decide

end DivisibilityBy3OQ02OQ01
