import Mathlib

/-
# Base-b Divisibility Rules (OQ-02)

## What This Proves
Generalizes divisibility rules to arbitrary bases:

1. **The (b-1) Rule**: n ≡ digit_sum_b(n) (mod b-1)
   In any base b ≥ 3, a number's digit sum determines its remainder mod (b-1).

2. **Specific Bases**: Divisibility tests for hex (mod 15), octal (mod 7).

3. **Factor Tests**: If d | (b-1), then d | n ↔ d | digit_sum_b(n).

## Key Mathematical Insight
Since b ≡ 1 (mod b-1), every power b^k ≡ 1 (mod b-1).
Therefore n = ∑ dᵢ · b^i ≡ ∑ dᵢ (mod b-1).

This is the universal principle behind casting out 9s (base 10),
casting out 7s (base 8), casting out 15s (base 16), etc.

## Status
- [x] Helper: b % (b-1) = 1 for b ≥ 3
- [x] General b-1 divisibility rule
- [x] Concrete base examples (hex, octal)
- [x] Divisibility iff form for b-1
- [x] Factor divisibility tests
- [x] Cross-base divisibility
- [x] Numerical verifications
- [x] Compatibility with parent file

## Mathlib Dependencies
- `Nat.modEq_digits_sum` : n ≡ (digits b n).sum [MOD d] when b % d = 1
- `Nat.dvd_iff_dvd_digits_sum` : d ∣ n ↔ d ∣ (digits b n).sum when b % d = 1
-/

namespace DivisibilityBy3OQ02

-- ============================================================
-- Part I: Key Helper Lemma
-- ============================================================

/-- For b ≥ 3, b ≡ 1 (mod b-1).
    Proof: b = 1 + (b-1), so b % (b-1) = 1 % (b-1) = 1 (since b-1 ≥ 2). -/
lemma base_mod_pred (b : ℕ) (hb : 3 ≤ b) : b % (b - 1) = 1 := by
  rw [Nat.mod_eq_sub_mod (by omega), show b - (b - 1) = 1 from by omega]
  exact Nat.mod_eq_of_lt (by omega)

/-- For d ≥ 2 dividing (b-1), we have b % d = 1.
    Proof: b = (b-1) + 1 = k*d + 1, so b mod d = 1 mod d = 1. -/
lemma factor_mod (b d : ℕ) (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hdiv : d ∣ (b - 1)) : b % d = 1 := by
  obtain ⟨k, hk⟩ := hdiv
  have hk_pos : 1 ≤ k := by
    by_contra h; push_neg at h; interval_cases k; omega
  have hb_eq : b = d * k + 1 := by omega
  rw [hb_eq, show d * k + 1 = 1 + d * k from by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

-- ============================================================
-- Part II: The Universal (b-1) Divisibility Rule
-- ============================================================

/-- **The (b-1) Rule**: In base b ≥ 3, a number is congruent to
    the sum of its base-b digits modulo (b-1). -/
theorem modEq_digits_sum_base_minus_one (b : ℕ) (hb : 3 ≤ b) (n : ℕ) :
    n ≡ (Nat.digits b n).sum [MOD (b - 1)] :=
  Nat.modEq_digits_sum (b - 1) b (base_mod_pred b hb) n

/-- **Divisibility by (b-1)**: (b-1) divides n iff (b-1) divides
    the base-b digit sum of n. -/
theorem dvd_base_minus_one_iff (b : ℕ) (hb : 3 ≤ b) (n : ℕ) :
    (b - 1) ∣ n ↔ (b - 1) ∣ (Nat.digits b n).sum :=
  Nat.dvd_iff_dvd_digits_sum (b - 1) b (base_mod_pred b hb) n

/-- The remainder of n mod (b-1) equals the digit sum's remainder. -/
theorem mod_base_minus_one_eq (b : ℕ) (hb : 3 ≤ b) (n : ℕ) :
    n % (b - 1) = (Nat.digits b n).sum % (b - 1) :=
  modEq_digits_sum_base_minus_one b hb n

-- ============================================================
-- Part III: Divisibility by Factors of (b-1)
-- ============================================================

/-- For any divisor d ≥ 2 of (b-1), the digit sum test works.
    Example: in base 10, 3 | 9, so 3 | n ↔ 3 | digit_sum(n). -/
theorem dvd_factor_iff (b d : ℕ) (hb : 2 ≤ b) (hd : 2 ≤ d)
    (hdiv : d ∣ (b - 1)) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum :=
  Nat.dvd_iff_dvd_digits_sum d b (factor_mod b d hb hd hdiv) n

-- ============================================================
-- Part IV: Specific Base Examples
-- ============================================================

/-- **Hexadecimal (base 16)**: 15 | n ↔ 15 | hex_digit_sum(n) -/
theorem hex_div_15 (n : ℕ) : 15 ∣ n ↔ 15 ∣ (Nat.digits 16 n).sum :=
  dvd_base_minus_one_iff 16 (by omega) n

/-- In hex, 3 | n ↔ 3 | hex_digit_sum(n) (since 3 | 15) -/
theorem hex_div_3 (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 16 n).sum :=
  dvd_factor_iff 16 3 (by omega) (by omega) ⟨5, by omega⟩ n

/-- In hex, 5 | n ↔ 5 | hex_digit_sum(n) (since 5 | 15) -/
theorem hex_div_5 (n : ℕ) : 5 ∣ n ↔ 5 ∣ (Nat.digits 16 n).sum :=
  dvd_factor_iff 16 5 (by omega) (by omega) ⟨3, by omega⟩ n

/-- **Octal (base 8)**: 7 | n ↔ 7 | oct_digit_sum(n) -/
theorem oct_div_7 (n : ℕ) : 7 ∣ n ↔ 7 ∣ (Nat.digits 8 n).sum :=
  dvd_base_minus_one_iff 8 (by omega) n

/-- Hex remainder: n % 15 = hex_digit_sum(n) % 15 -/
theorem hex_mod_15 (n : ℕ) : n % 15 = (Nat.digits 16 n).sum % 15 :=
  mod_base_minus_one_eq 16 (by omega) n

/-- Octal remainder: n % 7 = oct_digit_sum(n) % 7 -/
theorem oct_mod_7 (n : ℕ) : n % 7 = (Nat.digits 8 n).sum % 7 :=
  mod_base_minus_one_eq 8 (by omega) n

-- ============================================================
-- Part V: Numerical Verifications
-- ============================================================

/-- 255 = 0xFF. Hex digits sum to 30. 15 | 255 since 15 | 30. -/
example : 15 ∣ 255 := by rw [hex_div_15]; native_decide

/-- 256 = 0x100. Hex digits sum to 1. 15 ∤ 256. -/
example : ¬(15 ∣ 256) := by rw [hex_div_15]; native_decide

/-- 511 = 0o777. Oct digits sum to 21. 7 | 511 since 7 | 21. -/
example : 7 ∣ 511 := by rw [oct_div_7]; native_decide

-- ============================================================
-- Part VI: Cross-Base Divisibility
-- ============================================================

/-- If d divides both (b₁ - 1) and (b₂ - 1), then d | n can be
    tested via digit sums in EITHER base. -/
theorem cross_base_divisibility (b₁ b₂ d : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂)
    (hd : 2 ≤ d) (hd₁ : d ∣ (b₁ - 1)) (hd₂ : d ∣ (b₂ - 1)) (n : ℕ) :
    d ∣ (Nat.digits b₁ n).sum ↔ d ∣ (Nat.digits b₂ n).sum := by
  rw [← dvd_factor_iff b₁ d hb₁ hd hd₁ n, dvd_factor_iff b₂ d hb₂ hd hd₂ n]

/-- 3 | n can be tested in base 10 or base 16 -/
example (n : ℕ) : 3 ∣ (Nat.digits 10 n).sum ↔ 3 ∣ (Nat.digits 16 n).sum :=
  cross_base_divisibility 10 16 3 (by omega) (by omega) (by omega)
    ⟨3, by omega⟩ ⟨5, by omega⟩ n

-- ============================================================
-- Part VII: Consistency with Parent
-- ============================================================

/-- Matches parent's divisibility-by-3 rule. -/
theorem consistent_div3 (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum :=
  dvd_factor_iff 10 3 (by omega) (by omega) ⟨3, by omega⟩ n

/-- Matches parent's divisibility-by-9 rule. -/
theorem consistent_div9 (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum :=
  dvd_base_minus_one_iff 10 (by omega) n

end DivisibilityBy3OQ02
