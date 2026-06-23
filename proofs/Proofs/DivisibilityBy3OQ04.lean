import Mathlib

/-
# Practical Applications of the Generalized Divisibility Theorem (OQ-04)

## What This Proves
Formalizes the most important practical application of digit-sum congruences:
**casting out nines** (and its generalizations) for verifying arithmetic.

1. **General Casting Out**: Digit sums respect addition and multiplication mod d
2. **Casting Out Nines**: The classical base-10 mod-9 specialization
3. **Error Detection**: If the digit-sum check fails, the arithmetic is wrong
4. **Specific Applications**: Casting out sevens (octal), fifteens (hex), threes

## Historical Context
"Casting out nines" was the primary method for checking arithmetic calculations
from al-Khwārizmī (c. 825) through the 20th century. The method works because
n ≡ digit_sum(n) (mod 9), so arithmetic operations on digit sums mirror
operations on the original numbers modulo 9. Any discrepancy proves the
original computation was wrong.

## Status
- [x] General casting out for arbitrary base (addition and multiplication)
- [x] Casting out nines (base-10 specialization)
- [x] Error detection (contrapositives)
- [x] Specific base applications (octal, hex, threes)
- [x] Concrete examples with native_decide

## Mathlib Dependencies
- `Nat.modEq_digits_sum` : n ≡ (digits b n).sum [MOD d] when b % d = 1
- `Nat.add_mod` : (a + b) % n = ((a % n) + (b % n)) % n
- `Nat.mul_mod` : (a * b) % n = ((a % n) * (b % n)) % n
-/

namespace DivisibilityBy3OQ04

-- ============================================================
-- Part I: General Casting Out (Arbitrary Base and Modulus)
-- ============================================================

/-- **General digit sums respect addition.**
    For any base b and modulus d with b % d = 1:
    digit_sum_b(a) + digit_sum_b(c) ≡ digit_sum_b(a + c) (mod d).

    This is the universal principle behind all "casting out" methods. -/
theorem digit_sum_add_general (d b : ℕ) (hmod : b % d = 1) (a c : ℕ) :
    (Nat.digits b a).sum + (Nat.digits b c).sum ≡ (Nat.digits b (a + c)).sum [MOD d] := by
  show ((Nat.digits b a).sum + (Nat.digits b c).sum) % d =
       (Nat.digits b (a + c)).sum % d
  rw [Nat.add_mod,
      ← Nat.modEq_digits_sum d b hmod a,
      ← Nat.modEq_digits_sum d b hmod c,
      ← Nat.add_mod]
  exact Nat.modEq_digits_sum d b hmod (a + c)

/-- **General digit sums respect multiplication.**
    digit_sum_b(a) * digit_sum_b(c) ≡ digit_sum_b(a * c) (mod d). -/
theorem digit_sum_mul_general (d b : ℕ) (hmod : b % d = 1) (a c : ℕ) :
    (Nat.digits b a).sum * (Nat.digits b c).sum ≡ (Nat.digits b (a * c)).sum [MOD d] := by
  show ((Nat.digits b a).sum * (Nat.digits b c).sum) % d =
       (Nat.digits b (a * c)).sum % d
  rw [Nat.mul_mod,
      ← Nat.modEq_digits_sum d b hmod a,
      ← Nat.modEq_digits_sum d b hmod c,
      ← Nat.mul_mod]
  exact Nat.modEq_digits_sum d b hmod (a * c)

/-- **General error detection for addition.**
    If digit_sum_b(a) + digit_sum_b(c) is not congruent to digit_sum_b(r) mod d,
    then a + c ≠ r. -/
theorem detect_add_error_general (d b : ℕ) (hmod : b % d = 1) {a c r : ℕ}
    (hfail : ¬((Nat.digits b a).sum + (Nat.digits b c).sum ≡ (Nat.digits b r).sum [MOD d])) :
    a + c ≠ r :=
  fun heq => hfail (heq ▸ digit_sum_add_general d b hmod a c)

/-- **General error detection for multiplication.** -/
theorem detect_mul_error_general (d b : ℕ) (hmod : b % d = 1) {a c r : ℕ}
    (hfail : ¬((Nat.digits b a).sum * (Nat.digits b c).sum ≡ (Nat.digits b r).sum [MOD d])) :
    a * c ≠ r :=
  fun heq => hfail (heq ▸ digit_sum_mul_general d b hmod a c)

-- ============================================================
-- Part II: Casting Out Nines (Base 10, Mod 9)
-- ============================================================

/-- **Digit sums respect addition modulo 9.**
    digit_sum(a) + digit_sum(b) ≡ digit_sum(a + b) (mod 9).
    This is the foundation of "casting out nines" for checking addition.

    Historical use: After computing a + b = c by hand, check that
    digit_sum(a) + digit_sum(b) ≡ digit_sum(c) (mod 9). -/
theorem digit_sum_add (a b : ℕ) :
    (Nat.digits 10 a).sum + (Nat.digits 10 b).sum ≡ (Nat.digits 10 (a + b)).sum [MOD 9] :=
  digit_sum_add_general 9 10 (by native_decide) a b

/-- **Digit sums respect multiplication modulo 9.**
    digit_sum(a) * digit_sum(b) ≡ digit_sum(a * b) (mod 9).
    Casting out nines for checking multiplication. -/
theorem digit_sum_mul (a b : ℕ) :
    (Nat.digits 10 a).sum * (Nat.digits 10 b).sum ≡ (Nat.digits 10 (a * b)).sum [MOD 9] :=
  digit_sum_mul_general 9 10 (by native_decide) a b

/-- **Verification form for addition**: If a + b = c, then digit sums are consistent. -/
theorem casting_nines_add {a b c : ℕ} (h : a + b = c) :
    (Nat.digits 10 a).sum + (Nat.digits 10 b).sum ≡ (Nat.digits 10 c).sum [MOD 9] := by
  subst h; exact digit_sum_add a b

/-- **Verification form for multiplication**: If a * b = c, then digit sums are consistent. -/
theorem casting_nines_mul {a b c : ℕ} (h : a * b = c) :
    (Nat.digits 10 a).sum * (Nat.digits 10 b).sum ≡ (Nat.digits 10 c).sum [MOD 9] := by
  subst h; exact digit_sum_mul a b

-- ============================================================
-- Part III: Error Detection (Casting Out Nines)
-- ============================================================

/-- **Error detection for addition**: If the digit-sum check fails,
    the claimed sum is wrong. This is the contrapositive of casting_nines_add.

    Example: Someone claims 123 + 456 = 580. We check:
    digit_sum(123) + digit_sum(456) = 6 + 15 = 21, 21 % 9 = 3.
    digit_sum(580) = 13, 13 % 9 = 4. Since 3 ≠ 4, the sum is wrong. -/
theorem detect_add_error {a b c : ℕ}
    (h : ¬((Nat.digits 10 a).sum + (Nat.digits 10 b).sum ≡ (Nat.digits 10 c).sum [MOD 9])) :
    a + b ≠ c :=
  detect_add_error_general 9 10 (by native_decide) h

/-- **Error detection for multiplication**: If the digit-sum check fails,
    the claimed product is wrong. -/
theorem detect_mul_error {a b c : ℕ}
    (h : ¬((Nat.digits 10 a).sum * (Nat.digits 10 b).sum ≡ (Nat.digits 10 c).sum [MOD 9])) :
    a * b ≠ c :=
  detect_mul_error_general 9 10 (by native_decide) h

-- ============================================================
-- Part IV: Specific Base Applications
-- ============================================================

/-- **Casting out sevens (octal)**: In base 8, digit sums check arithmetic mod 7.
    Useful for checking octal arithmetic in computing contexts. -/
theorem octal_digit_sum_add (a b : ℕ) :
    (Nat.digits 8 a).sum + (Nat.digits 8 b).sum ≡ (Nat.digits 8 (a + b)).sum [MOD 7] :=
  digit_sum_add_general 7 8 (by native_decide) a b

/-- Casting out sevens for multiplication. -/
theorem octal_digit_sum_mul (a b : ℕ) :
    (Nat.digits 8 a).sum * (Nat.digits 8 b).sum ≡ (Nat.digits 8 (a * b)).sum [MOD 7] :=
  digit_sum_mul_general 7 8 (by native_decide) a b

/-- **Casting out fifteens (hexadecimal)**: In base 16, digit sums check arithmetic mod 15. -/
theorem hex_digit_sum_add (a b : ℕ) :
    (Nat.digits 16 a).sum + (Nat.digits 16 b).sum ≡ (Nat.digits 16 (a + b)).sum [MOD 15] :=
  digit_sum_add_general 15 16 (by native_decide) a b

/-- **Casting out threes**: Digit sums also check arithmetic mod 3 in base 10.
    Historically less common than nines but equally valid, since 3 | 9. -/
theorem casting_threes_add (a b : ℕ) :
    (Nat.digits 10 a).sum + (Nat.digits 10 b).sum ≡ (Nat.digits 10 (a + b)).sum [MOD 3] :=
  digit_sum_add_general 3 10 (by native_decide) a b

/-- Casting out threes for multiplication. -/
theorem casting_threes_mul (a b : ℕ) :
    (Nat.digits 10 a).sum * (Nat.digits 10 b).sum ≡ (Nat.digits 10 (a * b)).sum [MOD 3] :=
  digit_sum_mul_general 3 10 (by native_decide) a b

-- ============================================================
-- Part V: Concrete Examples and Verifications
-- ============================================================

/-- Verify 123 + 456 = 579 using casting out nines.
    digit_sum(123) = 6, digit_sum(456) = 15, digit_sum(579) = 21.
    (6 + 15) % 9 = 21 % 9 = 3 ✓ -/
example : (Nat.digits 10 123).sum + (Nat.digits 10 456).sum ≡
    (Nat.digits 10 579).sum [MOD 9] :=
  casting_nines_add rfl

/-- Detect error: 123 + 456 ≠ 580.
    digit_sum(580) = 13, (6 + 15) % 9 = 3 ≠ 13 % 9 = 4.
    The check catches the off-by-one error. -/
example : 123 + 456 ≠ 580 :=
  detect_add_error (by native_decide)

/-- Verify 12 × 13 = 156 using casting out nines.
    digit_sum(12) = 3, digit_sum(13) = 4, digit_sum(156) = 12.
    (3 × 4) % 9 = 12 % 9 = 3 ✓ -/
example : (Nat.digits 10 12).sum * (Nat.digits 10 13).sum ≡
    (Nat.digits 10 156).sum [MOD 9] :=
  casting_nines_mul rfl

/-- Detect multiplication error: 12 × 13 ≠ 157.
    digit_sum(157) = 13, (3 × 4) % 9 = 3 ≠ 13 % 9 = 4. -/
example : 12 * 13 ≠ 157 :=
  detect_mul_error (by native_decide)

/-- Verify 999 × 999 = 998001.
    digit_sum(999) = 27, digit_sum(998001) = 27.
    (27 × 27) % 9 = 0 = 27 % 9 ✓ -/
example : (Nat.digits 10 999).sum * (Nat.digits 10 999).sum ≡
    (Nat.digits 10 998001).sum [MOD 9] :=
  casting_nines_mul rfl

/-- **Limitation**: Casting out nines cannot detect errors that are multiples of 9.
    579 and 588 have the same digit sum mod 9 (both ≡ 3 mod 9).
    The method has no false positives (detected errors are real) but has
    false negatives (some errors go undetected). -/
example : (Nat.digits 10 579).sum % 9 = (Nat.digits 10 588).sum % 9 := by native_decide

/-- Casting out threes catches MORE errors than nines (since 3 | 9).
    The same error 123 + 456 ≠ 580 is also detected mod 3. -/
example : 123 + 456 ≠ 580 :=
  detect_add_error_general 3 10 (by native_decide) (by native_decide)

-- ============================================================
-- Part VI: Consistency with Parent
-- ============================================================

/-- The casting-out-nines add theorem is a special case of the general theorem
    with d = 9, b = 10, confirming consistency with the parent's
    divisibility-by-9 rule. -/
theorem consistent_with_parent_div9 (n : ℕ) :
    n ≡ (Nat.digits 10 n).sum [MOD 9] :=
  Nat.modEq_digits_sum 9 10 (by native_decide) n

/-- Consistency with parent's divisibility-by-3 rule. -/
theorem consistent_with_parent_div3 (n : ℕ) :
    n ≡ (Nat.digits 10 n).sum [MOD 3] :=
  Nat.modEq_digits_sum 3 10 (by native_decide) n

end DivisibilityBy3OQ04
