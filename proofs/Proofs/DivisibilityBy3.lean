import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

/-!
# Divisibility by 3 Rule (Wiedijk #85)

## What This Proves
A natural number is divisible by 3 if and only if the sum of its digits (in base 10)
is divisible by 3.

$$3 | n \iff 3 | \text{(sum of digits of } n \text{)}$$

More generally: $n \equiv \text{(digit sum)} \pmod 3$

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Nat.three_dvd_iff` which directly proves
  the divisibility-by-3 rule using digit representation.
- **Key Insight:** Since 10 ≡ 1 (mod 3), we have 10^k ≡ 1 (mod 3) for all k.
  Therefore if n = d₀ + d₁·10 + d₂·10² + ..., then n ≡ d₀ + d₁ + d₂ + ... (mod 3).
- **Proof Techniques:** Modular arithmetic, digit representation, induction on digit list.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves corollaries (divisibility by 9)
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Nat.digits` : Digit representation in arbitrary base
- `Nat.three_dvd_iff` : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum
- `Nat.nine_dvd_iff` : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum
- `Nat.modEq_three_digits_sum` : n ≡ (digits 10 n).sum [MOD 3]
- `Nat.modEq_nine_digits_sum` : n ≡ (digits 10 n).sum [MOD 9]

## Historical Note
The divisibility-by-3 rule has been known since ancient times and appears in many
cultures' mathematical traditions. It's one of the most practical divisibility tests,
easily performed mentally by summing digits.

This is #85 on Wiedijk's list of 100 theorems.
-/

namespace DivisibilityBy3

/-! ## The Key Insight: Why This Works

The magic behind divisibility by 3 comes from a simple observation about base 10:

  10 ≡ 1 (mod 3)

This means 10^k ≡ 1^k = 1 (mod 3) for any k ≥ 0.

When we write a number n in base 10:
  n = d₀ + d₁·10 + d₂·10² + d₃·10³ + ...

Taking both sides modulo 3:
  n ≡ d₀ + d₁·1 + d₂·1 + d₃·1 + ... (mod 3)
  n ≡ d₀ + d₁ + d₂ + d₃ + ... (mod 3)
  n ≡ (sum of digits) (mod 3)

Therefore: 3 | n ⟺ 3 | (sum of digits)
-/

/-! ## The Main Theorem: Divisibility by 3 Rule -/

/-- **Divisibility by 3 Rule (Wiedijk #85)**

A natural number n is divisible by 3 if and only if the sum of its decimal digits
is divisible by 3.

Example: 123 has digit sum 1+2+3 = 6, and 3 | 6, so 3 | 123. Indeed, 123 = 3 × 41. -/
theorem divisibility_by_3 (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum :=
  Nat.three_dvd_iff n

/-- The congruence form: n is congruent to its digit sum modulo 3. -/
theorem modEq_three_digits (n : ℕ) : n ≡ (Nat.digits 10 n).sum [MOD 3] :=
  Nat.modEq_three_digits_sum n

/-! ## Corollary: Divisibility by 9 Rule

The same principle applies to 9, since 10 ≡ 1 (mod 9) as well.
This gives us the classic "casting out nines" technique. -/

/-- **Divisibility by 9 Rule**

A natural number n is divisible by 9 if and only if the sum of its decimal digits
is divisible by 9.

Example: 729 has digit sum 7+2+9 = 18, and 9 | 18, so 9 | 729. Indeed, 729 = 9 × 81. -/
theorem divisibility_by_9 (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum :=
  Nat.nine_dvd_iff n

/-- The congruence form: n is congruent to its digit sum modulo 9. -/
theorem modEq_nine_digits (n : ℕ) : n ≡ (Nat.digits 10 n).sum [MOD 9] :=
  Nat.modEq_nine_digits_sum n

/-! ## The General Principle

The divisibility rules for 3 and 9 are special cases of a general theorem:
For any base b and divisor d where b ≡ 1 (mod d), we have n ≡ (digit sum in base b) (mod d). -/

/-- **Generalized Divisibility Rule**

For any base b ≥ 2 and any d > 0 such that b % d = 1,
a number n is congruent to the sum of its base-b digits modulo d. -/
theorem modEq_digits_sum_general (d b : ℕ) (_hb : 2 ≤ b) (_hd : 0 < d) (h : b % d = 1) (n : ℕ) :
    n ≡ (Nat.digits b n).sum [MOD d] :=
  Nat.modEq_digits_sum d b h n

/-- **Generalized Divisibility Rule (iff form)**

For any base b ≥ 2 and any d > 0 such that b % d = 1,
d divides n if and only if d divides the sum of n's base-b digits. -/
theorem dvd_iff_dvd_digits_sum_general (d b : ℕ) (_hb : 2 ≤ b) (_hd : 0 < d) (h : b % d = 1) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum :=
  Nat.dvd_iff_dvd_digits_sum d b h n

/-! ## Examples and Verification

Let's verify the divisibility rules with concrete examples. -/

/-- 123 is divisible by 3 (digits sum to 1+2+3 = 6) -/
example : 3 ∣ 123 := by
  rw [divisibility_by_3]
  native_decide

/-- 123 is not divisible by 9 (digits sum to 6, and 9 ∤ 6) -/
example : ¬(9 ∣ 123) := by
  rw [divisibility_by_9]
  native_decide

/-- 729 is divisible by 9 (digits sum to 7+2+9 = 18) -/
example : 9 ∣ 729 := by
  rw [divisibility_by_9]
  native_decide

/-- 729 = 3^6 is also divisible by 3 -/
example : 3 ∣ 729 := by
  rw [divisibility_by_3]
  native_decide

/-- 1000 is not divisible by 3 (digits sum to 1) -/
example : ¬(3 ∣ 1000) := by
  rw [divisibility_by_3]
  native_decide

/-- 999 is divisible by both 3 and 9 (digits sum to 27) -/
example : 3 ∣ 999 ∧ 9 ∣ 999 := by
  constructor
  · rw [divisibility_by_3]; native_decide
  · rw [divisibility_by_9]; native_decide

/-- 12345 is divisible by 3 (1+2+3+4+5 = 15) but not by 9 -/
example : 3 ∣ 12345 ∧ ¬(9 ∣ 12345) := by
  constructor
  · rw [divisibility_by_3]; native_decide
  · rw [divisibility_by_9]; native_decide

/-! ## Digit Representation Properties

Understanding how digits work is key to seeing why the rule holds. -/

/-- The digits of 123 in base 10 are [3, 2, 1] (least significant first) -/
example : Nat.digits 10 123 = [3, 2, 1] := by native_decide

/-- The sum of digits of 123 is 6 -/
example : (Nat.digits 10 123).sum = 6 := by native_decide

/-- The digits of 1000 are [0, 0, 0, 1] -/
example : Nat.digits 10 1000 = [0, 0, 0, 1] := by native_decide

/-- Zero has no digits (empty list) -/
example : Nat.digits 10 0 = [] := by native_decide

/-- Single-digit numbers have one digit -/
example : Nat.digits 10 7 = [7] := by native_decide

/-! ## Why It Works: The Proof Idea

The proof relies on two key facts:

1. **Base Representation**: Any natural number n can be written as
   n = Nat.ofDigits 10 (Nat.digits 10 n)

2. **Modular Equivalence of Base**:
   10 ≡ 1 (mod 3) and 10 ≡ 1 (mod 9)

   This means when we expand n = d₀ + 10·d₁ + 10²·d₂ + ...,
   modulo 3 (or 9), each power of 10 contributes just 1.

   Therefore: n ≡ d₀ + d₁ + d₂ + ... ≡ (digit sum) (mod 3 or 9)
-/

/-- 10 ≡ 1 (mod 3) -/
example : 10 % 3 = 1 := by native_decide

/-- 10 ≡ 1 (mod 9) -/
example : 10 % 9 = 1 := by native_decide

/-- 100 ≡ 1 (mod 3) -/
example : 100 % 3 = 1 := by native_decide

/-- 100 ≡ 1 (mod 9) -/
example : 100 % 9 = 1 := by native_decide

/-! ## Applications: Iterative Digit Sums

A practical application: you can repeatedly sum digits until you get a single digit.
The result (called the digital root) determines divisibility by 3 and 9. -/

/-- If a number's digits sum to a value, and that value is divisible by 3,
    then the original number is divisible by 3. -/
theorem div_3_of_digit_sum_div_3 {n : ℕ} (h : 3 ∣ (Nat.digits 10 n).sum) : 3 ∣ n :=
  (divisibility_by_3 n).mpr h

/-- If a number's digits sum to a value, and that value is divisible by 9,
    then the original number is divisible by 9. -/
theorem div_9_of_digit_sum_div_9 {n : ℕ} (h : 9 ∣ (Nat.digits 10 n).sum) : 9 ∣ n :=
  (divisibility_by_9 n).mpr h

/-- Transitivity: if 3 divides a number, it divides its digit sum -/
theorem digit_sum_div_3_of_div_3 {n : ℕ} (h : 3 ∣ n) : 3 ∣ (Nat.digits 10 n).sum :=
  (divisibility_by_3 n).mp h

/-- Transitivity: if 9 divides a number, it divides its digit sum -/
theorem digit_sum_div_9_of_div_9 {n : ℕ} (h : 9 ∣ n) : 9 ∣ (Nat.digits 10 n).sum :=
  (divisibility_by_9 n).mp h

#check divisibility_by_3
#check divisibility_by_9
#check modEq_three_digits
#check modEq_nine_digits

end DivisibilityBy3
